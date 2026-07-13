use qed_analysis::layout::{AccountLayout, FieldKind};

use super::core::{Atom, Expr, Width};
use super::emit::{atoms_to_lean, fold_abstractions};
use super::input::{resolve_layout, DescriptorOp, RefinementDescriptor};

// ════════════════════════════════════════════════════════════════
// Refinement codegen — mechanically emit the per-arm `AsmRefines…` obligation theorem.
// Detects mutated cells, classifies codec (token/mint/counter/vault), walks the layout.
// Returns `(module_name, lean)` or `None` for unregistered arms / unrecognized layouts.
// ════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, PartialEq, Eq)]
enum CodecKind {
    Token,
    Mint,
    Counter,
    Vault,
}

struct RefineSpec {
    asm_pred: &'static str,
    /// account roles in `AsmRefines…` argument order.
    accounts: &'static [(&'static str, CodecKind)],
}

/// The per-lift read-only bundle every refinement/transition emitter consumes:
/// the lift's module name, pre/post atoms, abstraction substitution, symbolic
/// params, CU/PC shape and the layout sources. One struct instead of ten
/// positional arguments threaded through the codegen.
#[derive(Clone, Copy)]
pub(super) struct RefinementCtx<'a> {
    pub(super) lift_module: &'a str,
    pub(super) pre: &'a [Atom],
    /// Cleaned post atoms of the refinement target (`post_clean`, or the
    /// transition target's post).
    pub(super) post: &'a [Atom],
    pub(super) abs_subst: &'a std::collections::BTreeMap<String, String>,
    pub(super) vars: &'a [String],
    pub(super) n_cu: usize,
    pub(super) start_pc: usize,
    pub(super) exit_pc: usize,
    pub(super) idl: Option<&'a serde_json::Value>,
    // qedrecover-emitted layouts; preferred over `idl` for account-codec offsets (#41 loop closure).
    pub(super) sidecar_layouts: Option<&'a [AccountLayout]>,
}

fn refine_registry(arm: &str) -> Option<RefineSpec> {
    match arm {
        // Token/mint arms target the layout-general N-account predicate (#25):
        // one `(base, preFields, postFields)` triple per account, emitted
        // directly off the lift on the vault route — no bespoke record predicate.
        "Transfer" | "TransferChecked" => Some(RefineSpec {
            asm_pred: "AsmRefinesFieldUpdates",
            accounts: &[("src", CodecKind::Token), ("dst", CodecKind::Token)],
        }),
        "MintTo" => Some(RefineSpec {
            asm_pred: "AsmRefinesFieldUpdates",
            accounts: &[("mint", CodecKind::Mint), ("dest", CodecKind::Token)],
        }),
        "Burn" => Some(RefineSpec {
            asm_pred: "AsmRefinesFieldUpdates",
            accounts: &[("account", CodecKind::Token), ("mint", CodecKind::Mint)],
        }),
        // Non-token single-field counter: codec is one u64 (coarse=fine, no aggregation).
        // Constant +1 delta handled by `counterIncrement` clean-up + `emit_counter_refinement`.
        "counterIncrement" => Some(RefineSpec {
            asm_pred: "AsmRefinesCounterIncrement",
            accounts: &[("counter", CodecKind::Counter)],
        }),
        // Multi-field non-token account (IDL-driven). `AsmRefinesFieldUpdate` proved by reshaping
        // via `account_agg` and framing untouched fields — `emit_vault_refinement`.
        "VaultIncrement" => Some(RefineSpec {
            asm_pred: "AsmRefinesFieldUpdate",
            accounts: &[("vault", CodecKind::Vault)],
        }),
        _ => None,
    }
}

/// True for arms with a constant `+1` delta (counter/vault). Gates the delta-cleaning so arms
/// like `two_op`'s `+1` are not mistakenly cleaned.
pub(super) fn is_const_delta_arm(arm: Option<&str>) -> bool {
    arm.and_then(refine_registry).map_or(false, |s| {
        s.accounts
            .iter()
            .all(|(_, c)| matches!(c, CodecKind::Counter | CodecKind::Vault))
    })
}

/// Value of a memory cell at `(base_raw, off)` with the given byte-ness,
/// if the lift owns it.
pub(super) fn cell_val<'a>(
    atoms: &'a [Atom],
    base_raw: &str,
    off: i64,
    byte: bool,
) -> Option<&'a Expr> {
    for a in atoms {
        if let Atom::Mem {
            addr_base,
            addr_off,
            width,
            value,
            ..
        } = a
        {
            if *addr_off == off
                && matches!(width, Width::Byte) == byte
                && addr_base.to_lean() == base_raw
            {
                return Some(value);
            }
        }
    }
    None
}

/// A balance/supply cell mutated in the post (`a ± b`, both loaded).
struct MutCell {
    base: Expr,
    base_raw: String,
    off: i64,
    a: Expr,
    b: Expr,
    is_sub: bool,
}

/// A synthesized SPL account field for the N-account walker: pubkey scalar,
/// the mutated `u64`, or an opaque region (split against lift ownership).
enum SynthKind {
    Pubkey,
    U64Updated,
    Blob(i64),
}

/// One account's contribution to the N-account `AsmRefinesFieldUpdates`
/// obligation: `(base, preFields, postFields)` triple plus the frame atoms,
/// consumed lift cells and binders its reshape needs.
struct AcctFields {
    role: &'static str,       // registry role — names the `ensures_<role>` corollary
    base_arg: String,         // "(addr5 + 88)" — account base argument
    pre_fields: Vec<String>,  // rendered `(off, FieldVal)` entries, pre values
    post_fields: Vec<String>, // same with the mutated field shifted
    frame: Vec<String>,       // frame atoms (unowned scalars + blob gaps)
    owned: Vec<(String, i64, bool)>, // lift cells consumed (excluded from setup)
    params: Vec<String>,      // fresh Nat params (framed pubkey limbs)
    ba_params: Vec<String>,   // fresh ByteArray params (blob gaps)
    byte_hyps: Vec<String>,   // `< 256` hyps for owned blob bytes (codecValid)
    // Gap-size hyps `(name, "g.size = len")`: pin offsets so fine atoms land at lift's addresses.
    gap_size_hyps: Vec<(String, String)>,
    has_owned_segs: bool, // any `.byte`/`.u64` seg inside a blob (needs FieldSeg.size)
    field_off: i64,       // mutated `u64`'s offset within the account
    is_sub: bool,         // debit (`-`) vs credit (`+`)
}

pub(super) fn emit_refinement(
    arm_name: &str,
    ctx: RefinementCtx<'_>,
    // Returns `(refine_module, refine_lean)`.
) -> Option<(String, String)> {
    let spec = refine_registry(arm_name)?;

    // Counter codec (single u64, coarse=fine): dedicated path keeps token/mint codegen byte-identical.
    if spec
        .accounts
        .iter()
        .all(|(_, c)| matches!(c, CodecKind::Counter))
    {
        return emit_counter_refinement(&spec, ctx);
    }

    // Vault codec (IDL layout, multi-field): owns updated u64, frames the rest, reshapes via `account_agg`.
    if spec
        .accounts
        .iter()
        .all(|(_, c)| matches!(c, CodecKind::Vault))
    {
        return emit_vault_refinement(&spec, ctx);
    }

    // Token/mint codecs: the vault route generalized to N accounts (#25) —
    // `AsmRefinesFieldUpdates` emitted directly off the lift, no aggregation module.
    emit_token_refinement(&spec, ctx)
}

/// Emit the N-account token/mint refinement (#25): one `(base, preFields,
/// postFields)` triple per registry account, targeting the layout-general
/// `AsmRefinesFieldUpdates`. Same mechanism as `emit_vault_refinement` —
/// reshape coarse→fine via `codecCoarse_eq_fine`, frame the untouched cells —
/// generalized to N accounts and to `.u64` segs inside opaque regions.
fn emit_token_refinement(spec: &RefineSpec, ctx: RefinementCtx<'_>) -> Option<(String, String)> {
    let RefinementCtx {
        lift_module,
        pre,
        post: post_clean,
        abs_subst,
        idl,
        sidecar_layouts,
        ..
    } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // ── Detect mutated account cells (a ± b, both InitMem) ──────────
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    let mut muts: Vec<MutCell> = Vec::new();
    for atom in post_clean {
        if let Atom::Mem {
            addr_base,
            addr_off,
            value,
            ..
        } = atom
        {
            let (a, b, is_sub) = match value {
                Expr::CleanSub(a, b) => ((**a).clone(), (**b).clone(), true),
                Expr::NatAdd(a, b) => ((**a).clone(), (**b).clone(), false),
                _ => continue,
            };
            if is_initmem(&a) && is_initmem(&b) {
                muts.push(MutCell {
                    base: addr_base.clone(),
                    base_raw: addr_base.to_lean(),
                    off: *addr_off,
                    a,
                    b,
                    is_sub,
                });
            }
        }
    }
    if muts.is_empty() {
        return None;
    }
    // The transferred amount `b` is shared across all mutated cells.
    let amount = fold(&muts[0].b);

    // SPL offsets from the IDL where available (fallback: amount@64 in a
    // 165-byte token account, supply@36 in an 82-byte mint).
    let (tok_amount_off, tok_size) = resolve_layout(sidecar_layouts, idl, "token")
        .and_then(|l| {
            let a = l.fields.iter().find(|f| f.name == "amount")?;
            Some((a.offset as i64, l.size as i64))
        })
        .unwrap_or((64, 165));
    let (mint_supply_off, mint_size) = resolve_layout(sidecar_layouts, idl, "mint")
        .and_then(|l| {
            let s = l.fields.iter().find(|f| f.name == "supply")?;
            Some((s.offset as i64, l.size as i64))
        })
        .unwrap_or((36, 82));

    // ── Assign each registry account to a mutated cell; walk its layout ────────────────────────
    // Token amount cells have a mint dword at off-64; mint supply cells have is_initialized at off+9.
    let is_mint_mut = |m: &MutCell| cell_val(pre, &m.base_raw, m.off + 9, true).is_some();
    let is_tok_mut = |m: &MutCell| cell_val(pre, &m.base_raw, m.off - 64, false).is_some();
    let mut used = vec![false; muts.len()];
    let mut accts: Vec<AcctFields> = Vec::new();
    let mut fresh = 0u32;
    for (role, codec) in spec.accounts {
        // Pick unused mutated cell for this codec; for two token accounts (Transfer), src=sub, dst=add.
        let want_sub = *role == "src" || *role == "account";
        let idx = (0..muts.len()).find(|&i| {
            !used[i]
                && match codec {
                    CodecKind::Token => {
                        is_tok_mut(&muts[i])
                            && (spec
                                .accounts
                                .iter()
                                .filter(|(_, c)| *c == CodecKind::Token)
                                .count()
                                < 2
                                || muts[i].is_sub == want_sub)
                    }
                    CodecKind::Mint => is_mint_mut(&muts[i]),
                    // All-counter / all-vault specs take their early
                    // `emit_*_refinement` paths; this loop only runs for
                    // token/mint codecs.
                    CodecKind::Counter | CodecKind::Vault => {
                        unreachable!("counter/vault codec handled by its own emitter")
                    }
                }
        })?;
        used[idx] = true;
        let m = &muts[idx];
        // Synthesized SPL layout: scalar fields + opaque regions covering the
        // remainder (split against lift ownership by `build_account_fields`).
        let (field_off, synth): (i64, Vec<(i64, SynthKind)>) = match codec {
            CodecKind::Token => (
                tok_amount_off,
                vec![
                    (0, SynthKind::Pubkey),
                    (32, SynthKind::Pubkey),
                    (tok_amount_off, SynthKind::U64Updated),
                    (
                        tok_amount_off + 8,
                        SynthKind::Blob(tok_size - tok_amount_off - 8),
                    ),
                ],
            ),
            CodecKind::Mint => (
                mint_supply_off,
                vec![
                    (0, SynthKind::Blob(mint_supply_off)),
                    (mint_supply_off, SynthKind::U64Updated),
                    (
                        mint_supply_off + 8,
                        SynthKind::Blob(mint_size - mint_supply_off - 8),
                    ),
                ],
            ),
            CodecKind::Counter | CodecKind::Vault => {
                unreachable!("counter/vault codec handled by its own emitter")
            }
        };
        accts.push(build_account_fields(
            ctx, m, &amount, field_off, &synth, &mut fresh, role,
        )?);
    }

    // ── Assemble setup atoms (lift cells not owned by any account) ──
    let owned: std::collections::HashSet<(String, i64, bool)> =
        accts.iter().flat_map(|b| b.owned.iter().cloned()).collect();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => owned.contains(&(addr_base.to_lean(), *addr_off, matches!(width, Width::Byte))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean
        .iter()
        .filter(|a| !is_owned(a))
        .cloned()
        .collect();

    let module = format!("{}Refinement", lift_module);
    let lean =
        render_token_refinement(spec, &module, &accts, ctx, &setup_pre, &setup_post, &amount);
    Some((module, lean))
}

/// Value of the `u64` cell at `(base_raw, off)`, if the lift owns one.
pub(super) fn cell_val_dword<'a>(atoms: &'a [Atom], base_raw: &str, off: i64) -> Option<&'a Expr> {
    atoms.iter().find_map(|a| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            value,
            ..
        } if *addr_off == off
            && matches!(width, Width::Dword)
            && addr_base.to_lean() == base_raw =>
        {
            Some(value)
        }
        _ => None,
    })
}

/// Walk one account's synthesized layout against the lift's owned cells.
/// Owned scalars flow through the fine codec (their values appear in the
/// field list); unowned scalars become framed params; opaque regions split
/// into owned `.u64`/`.byte` segs and framed `.gap`s, with gap-size
/// hypotheses pinning the running offsets (`segsSL`) to the lift's addresses.
fn build_account_fields(
    ctx: RefinementCtx<'_>,
    m: &MutCell,
    amount: &str,
    field_off: i64,
    synth: &[(i64, SynthKind)],
    fresh: &mut u32,
    role: &'static str,
) -> Option<AcctFields> {
    let RefinementCtx { pre, abs_subst, .. } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let base_off = m.off - field_off;
    let base_expr = fold(&m.base);
    let base_arg = if base_off == 0 {
        base_expr.clone()
    } else {
        format!("({} + {})", base_expr, base_off)
    };
    let mut a = AcctFields {
        role,
        base_arg,
        pre_fields: Vec::new(),
        post_fields: Vec::new(),
        frame: Vec::new(),
        owned: Vec::new(),
        params: Vec::new(),
        ba_params: Vec::new(),
        byte_hyps: Vec::new(),
        gap_size_hyps: Vec::new(),
        has_owned_segs: false,
        field_off,
        is_sub: m.is_sub,
    };
    for (off, kind) in synth {
        let abs = base_off + *off;
        match kind {
            SynthKind::U64Updated => {
                // The account's mutated cell must be this field.
                if abs != m.off {
                    return None;
                }
                let pre_v = fold(&m.a);
                let post_v = if m.is_sub {
                    format!("({} - {})", pre_v, amount)
                } else {
                    format!("({} + {})", pre_v, amount)
                };
                a.pre_fields.push(format!("({}, .u64 {})", off, pre_v));
                a.post_fields.push(format!("({}, .u64 {})", off, post_v));
                a.owned.push((m.base_raw.clone(), abs, false));
            }
            SynthKind::Pubkey => {
                if (0..4).all(|i| cell_val(pre, &m.base_raw, abs + 8 * i, false).is_some()) {
                    // Owned pubkey: its limbs flow through the fine codec.
                    let limbs: Vec<String> = (0..4)
                        .map(|i| {
                            a.owned.push((m.base_raw.clone(), abs + 8 * i, false));
                            fold(cell_val(pre, &m.base_raw, abs + 8 * i, false).unwrap())
                        })
                        .collect();
                    let rec = format!("⟨{}⟩", limbs.join(", "));
                    a.pre_fields.push(format!("({}, .pubkey {})", off, rec));
                    a.post_fields.push(format!("({}, .pubkey {})", off, rec));
                } else {
                    // Unread pubkey: fresh limb params, framed.
                    let limbs: Vec<String> = (0..4)
                        .map(|_| {
                            let p = format!("o{}", *fresh);
                            *fresh += 1;
                            a.params.push(p.clone());
                            p
                        })
                        .collect();
                    let rec = format!("⟨{}⟩", limbs.join(", "));
                    a.pre_fields.push(format!("({}, .pubkey {})", off, rec));
                    a.post_fields.push(format!("({}, .pubkey {})", off, rec));
                    for (i, limb) in limbs.iter().enumerate() {
                        a.frame.push(format!(
                            "(effectiveAddr {} {} ↦U64 {})",
                            base_expr,
                            abs + 8 * i as i64,
                            limb
                        ));
                    }
                }
            }
            SynthKind::Blob(len) => {
                let mut segs: Vec<String> = Vec::new();
                let mut cursor = 0i64; // end of the last owned seg (field-relative)
                let mut rel = 0i64;
                while rel < *len {
                    // Owned dword seg (only if fully inside the region), else owned byte seg.
                    let dw = if rel + 8 <= *len {
                        cell_val_dword(pre, &m.base_raw, abs + rel)
                    } else {
                        None
                    };
                    let by = if dw.is_none() {
                        cell_val(pre, &m.base_raw, abs + rel, true)
                    } else {
                        None
                    };
                    if dw.is_none() && by.is_none() {
                        rel += 1;
                        continue;
                    }
                    if rel > cursor {
                        // Gap before an owned seg: pin its size so `segsSL`
                        // places the following segs at the lift's addresses.
                        let g = format!("fg{}", *fresh);
                        *fresh += 1;
                        a.ba_params.push(g.clone());
                        a.gap_size_hyps.push((
                            format!("h{}_sz", g),
                            format!("{}.size = {}", g, rel - cursor),
                        ));
                        segs.push(format!(".gap {}", g));
                        a.frame.push(format!(
                            "(effectiveAddr {} {} ↦Bytes {})",
                            base_expr,
                            abs + cursor,
                            g
                        ));
                    }
                    if let Some(v) = dw {
                        segs.push(format!(".u64 ({})", fold(v)));
                        a.owned.push((m.base_raw.clone(), abs + rel, false));
                        rel += 8;
                    } else {
                        let val = fold(by.unwrap());
                        segs.push(format!(".byte ({})", val));
                        a.byte_hyps.push(format!("(h_b{} : {} < 256)", *fresh, val));
                        *fresh += 1;
                        a.owned.push((m.base_raw.clone(), abs + rel, true));
                        rel += 1;
                    }
                    a.has_owned_segs = true;
                    cursor = rel;
                }
                if cursor < *len {
                    // Trailing gap (last seg): no size hyp needed — free ByteArray.
                    let g = format!("fg{}", *fresh);
                    *fresh += 1;
                    a.ba_params.push(g.clone());
                    segs.push(format!(".gap {}", g));
                    a.frame.push(format!(
                        "(effectiveAddr {} {} ↦Bytes {})",
                        base_expr,
                        abs + cursor,
                        g
                    ));
                }
                let seglist = format!("[{}]", segs.join(", "));
                a.pre_fields.push(format!("({}, .blob {})", off, seglist));
                a.post_fields.push(format!("({}, .blob {})", off, seglist));
            }
        }
    }
    Some(a)
}

/// True iff `n` occurs in `hay` as a standalone identifier.
fn contains_ident(hay: &str, n: &str) -> bool {
    let ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    hay.match_indices(n).any(|(i, _)| {
        let bytes = hay.as_bytes();
        let before_ok = i == 0 || !ident(bytes[i - 1]);
        let after = i + n.len();
        let after_ok = after >= bytes.len() || !ident(bytes[after]);
        before_ok && after_ok
    })
}

/// Render the N-account token/mint refinement: `refines_asm` targeting
/// `AsmRefinesFieldUpdates` (proof: unfold the account fold, reshape each
/// coarse codec via `codecCoarse_eq_fine`, frame, `sl_exact`) plus one
/// `ensures_<role>` accessor corollary per account.
fn render_token_refinement(
    spec: &RefineSpec,
    module: &str,
    accts: &[AcctFields],
    ctx: RefinementCtx<'_>,
    setup_pre: &[Atom],
    setup_post: &[Atom],
    amount: &str,
) -> String {
    let RefinementCtx {
        pre,
        post: post_clean,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        ..
    } = ctx;
    let mut nat_params = vars.join(" ");
    for b in accts {
        for p in &b.params {
            nat_params.push(' ');
            nat_params.push_str(p);
        }
    }
    let ba_params: Vec<String> = accts
        .iter()
        .flat_map(|b| b.ba_params.iter().cloned())
        .collect();
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    for b in accts {
        for h in &b.byte_hyps {
            binders.push_str(&format!("\n    {}", h));
        }
    }
    for b in accts {
        for (name, prop) in &b.gap_size_hyps {
            binders.push_str(&format!("\n    ({} : {})", name, prop));
        }
    }

    // Account `(base, preFields, postFields)` triples, in registry order.
    let triples = accts
        .iter()
        .map(|b| {
            format!(
                "({},\n        [{}],\n        [{}])",
                b.base_arg,
                b.pre_fields.join(", "),
                b.post_fields.join(", ")
            )
        })
        .collect::<Vec<_>>()
        .join(",\n       ");

    let has_bytes = accts.iter().any(|b| !b.byte_hyps.is_empty());
    // Owned blob bytes leave `< 256` residuals after the codecValid simp → `omega`.
    let valid_tac = if has_bytes {
        "by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega"
    } else {
        "by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid]"
    };
    let mut rw: Vec<String> = Vec::new();
    for b in accts {
        rw.push(format!(
            "codecCoarse_eq_fine {}\n        [{}]\n        ({})",
            b.base_arg,
            b.pre_fields.join(", "),
            valid_tac
        ));
    }
    for b in accts {
        rw.push(format!(
            "codecCoarse_eq_fine {}\n        [{}]\n        ({})",
            b.base_arg,
            b.post_fields.join(", "),
            valid_tac
        ));
    }

    // Fine simp set: unfold the fine codec to scattered atoms and normalize
    // running blob offsets (`FieldSeg.size` + gap-size hyps) and account-base
    // additions (`Nat.add_assoc`/`Nat.reduceAdd`) to the lift's flat addresses.
    let mut fine: Vec<String> = vec![
        "codecFine".into(),
        "FieldVal.fine".into(),
        "pubkeyIs".into(),
        "segsSL".into(),
        "FieldSeg.sl".into(),
    ];
    if accts.iter().any(|b| b.has_owned_segs) {
        fine.push("FieldSeg.size".into());
    }
    for b in accts {
        for (name, _) in &b.gap_size_hyps {
            fine.push(name.clone());
        }
    }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    fine.push("Nat.add_assoc".into());
    fine.push("Nat.reduceAdd".into());
    let fine_simp = fine.join(", ");

    let frame_atoms: Vec<String> = accts.iter().flat_map(|b| b.frame.iter().cloned()).collect();
    let frame = frame_atoms.join(" **\n      ");
    let proof_tail = if frame_atoms.is_empty() {
        "  sl_exact lift".to_string()
    } else {
        format!(
            "  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  sl_exact framed"
        )
    };

    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    // One accessor corollary per account: the mutated `u64` shifts by `amount`.
    // Binders are filtered to the identifiers its field lists mention.
    let nat_pool: Vec<String> = {
        let mut p: Vec<String> = vars.to_vec();
        for b in accts {
            p.extend(b.params.iter().cloned());
        }
        p
    };
    let ensures = accts
        .iter()
        .map(|b| {
            let hay: Vec<&String> = b.pre_fields.iter().chain(b.post_fields.iter()).collect();
            let uses = |n: &String| hay.iter().any(|h| contains_ident(h, n));
            let ens_nat: Vec<String> = nat_pool.iter().filter(|n| uses(n)).cloned().collect();
            let ens_ba: Vec<String> = b.ba_params.iter().filter(|n| uses(n)).cloned().collect();
            let mut ens_binders = format!("({} : Nat)", ens_nat.join(" "));
            if !ens_ba.is_empty() {
                ens_binders.push_str(&format!("\n    ({} : ByteArray)", ens_ba.join(" ")));
            }
            let op = if b.is_sub { "-" } else { "+" };
            format!(
                "/-- qedgen `ensures`-shape for the `{role}` account, mechanically
    discharged: its `u64` field (offset {off}) shifts by `{amount}`. -/
theorem ensures_{role}
    {ens_binders} :
    u64FieldAt {off} [{post_list}]
      = u64FieldAt {off} [{pre_list}] {op} {amount} := by
  qedsvm_discharge",
                role = b.role,
                off = b.field_off,
                amount = amount,
                ens_binders = ens_binders,
                op = op,
                pre_list = b.pre_fields.join(", "),
                post_list = b.post_fields.join(", ")
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n");

    format!(
        "/-
  {pred} asm-refines theorem for the SPL token/mint arms. MECHANICALLY
  EMITTED by qedlift's refinement codegen from the lift's atoms + the IDL
  arm name. One `(base, preFields, postFields)` triple per account on the
  layout-general vault route: each coarse codec is reshaped to fine via
  `codecCoarse_eq_fine` (`account_agg`) and the untouched cells are framed —
  no bespoke record predicate, no aggregation module (#25).
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 1600000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    {binders}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr
      [{triples}]
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  simp only [SVM.Solana.Abstract.codecsPre, SVM.Solana.Abstract.codecsPost]
  rw [{rw}]
  simp only [{fine_simp}]
{proof_tail}

{ensures}

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        binders = binders,
        n = n_cu,
        entry = start_pc,
        exit = exit_pc,
        lift_pre = lift_pre,
        lift_post = lift_post,
        triples = triples,
        setup_pre = setup_pre_s,
        setup_post = setup_post_s,
        rw = rw.join(",\n      "),
        fine_simp = fine_simp,
        proof_tail = proof_tail,
        ensures = ensures,
    )
}

/// Emit a counter-codec refinement: single owned `u64` cell, constant +1 delta.
/// No aggregation (coarse = fine for `u64`), no frame, no `amount` arg.
fn emit_counter_refinement(spec: &RefineSpec, ctx: RefinementCtx<'_>) -> Option<(String, String)> {
    let RefinementCtx {
        lift_module,
        pre,
        post: post_clean,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        ..
    } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // Find the post-state incremented `u64` cell (NatAdd(InitMem, Const) form).
    let mut found: Option<(Expr, i64, Expr, i64)> = None;
    for atom in post_clean {
        if let Atom::Mem {
            addr_base,
            addr_off,
            width,
            value,
            ..
        } = atom
        {
            if matches!(width, Width::Dword) {
                if let Expr::NatAdd(a, b) = value {
                    if let (Expr::InitMem(_), Expr::Const(k)) = (a.as_ref(), b.as_ref()) {
                        found = Some(((*addr_base).clone(), *addr_off, (**a).clone(), *k));
                        break;
                    }
                }
            }
        }
    }
    let (base, off, pre_val, delta) = found?;
    let base_l = fold(&base);
    let addr_arg = if off == 0 {
        base_l.clone()
    } else {
        format!("({} + {})", base_l, off)
    };
    let counter_pre = fold(&pre_val);
    let record = format!("{{ counter := {} }}", counter_pre);

    // Owned `u64` cell flows through the codec's fine form; everything else stays in setup.
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => addr_base.to_lean() == owned_base && *addr_off == off && matches!(width, Width::Dword),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean
        .iter()
        .filter(|a| !is_owned(a))
        .cloned()
        .collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_counter_refinement(CounterRender {
        spec,
        module: &module,
        addr_arg: &addr_arg,
        record: &record,
        pre,
        post_clean,
        setup_pre: &setup_pre,
        setup_post: &setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        counter_pre: &counter_pre,
        delta,
    });
    Some((module, lean))
}

struct CounterRender<'a> {
    spec: &'a RefineSpec,
    module: &'a str,
    addr_arg: &'a str,
    record: &'a str,
    pre: &'a [Atom],
    post_clean: &'a [Atom],
    setup_pre: &'a [Atom],
    setup_post: &'a [Atom],
    abs_subst: &'a std::collections::BTreeMap<String, String>,
    vars: &'a [String],
    n_cu: usize,
    start_pc: usize,
    exit_pc: usize,
    counter_pre: &'a str,
    delta: i64,
}

/// Render the counter refinement theorem. Proof: `unfold` + `simp [counterValOf]` + `sl_exact`.
fn render_counter_refinement(r: CounterRender<'_>) -> String {
    let CounterRender {
        spec,
        module,
        addr_arg,
        record,
        pre,
        post_clean,
        setup_pre,
        setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        counter_pre,
        delta,
    } = r;
    let nat_params = vars.join(" ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
        "/-
  {pred} asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen — the first NON-token refinement. The counter
  account is a single `u64` field (coarse = fine, no codec aggregation),
  so the proof is `unfold` + `simp [counterValOf]` + `sl_exact` with no
  aggregation rewrite and no frame.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_params} : Nat)
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {addr}
      {record}
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  simp only [SVM.Solana.counterValOf_eq]
  sl_exact lift

/-- qedgen `ensures`-shape, mechanically discharged: the counter field
    shifts by {delta}. Pairs with `refines_asm`; the counter account is a
    single-`u64` field list, so the accessor projection is `u64FieldAt 0`. -/
theorem ensures ({counter_pre} : Nat) :
    u64FieldAt 0 [(0, .u64 ({counter_pre} + {delta}))]
      = u64FieldAt 0 [(0, .u64 {counter_pre})] + {delta} := by
  qedsvm_discharge

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        nat_params = nat_params,
        counter_pre = counter_pre,
        delta = delta,
        n = n_cu,
        entry = start_pc,
        exit = exit_pc,
        lift_pre = lift_pre,
        lift_post = lift_post,
        addr = addr_arg,
        record = record,
        setup_pre = setup_pre_s,
        setup_post = setup_post_s,
    )
}

/// Emit a vault (`AsmRefinesFieldUpdate`) refinement: owns the updated `u64`, frames the rest,
/// reshapes via `codecCoarse_eq_fine`. IDL-driven — new programs cost only a qedspec.
fn emit_vault_refinement(spec: &RefineSpec, ctx: RefinementCtx<'_>) -> Option<(String, String)> {
    let RefinementCtx {
        lift_module,
        pre,
        post: post_clean,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        idl,
        sidecar_layouts,
    } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let layout = resolve_layout(sidecar_layouts, idl, "vault")?;

    let mut updated: Option<(Expr, i64, Expr, i64)> = None; // base, off, pre_val, delta (NatAdd(InitMem, Const))
    for atom in post_clean {
        if let Atom::Mem {
            addr_base,
            addr_off,
            width,
            value,
            ..
        } = atom
        {
            if matches!(width, Width::Dword) {
                if let Expr::NatAdd(a, b) = value {
                    if let (Expr::InitMem(_), Expr::Const(k)) = (a.as_ref(), b.as_ref()) {
                        updated = Some(((*addr_base).clone(), *addr_off, (**a).clone(), *k));
                        break;
                    }
                }
            }
        }
    }
    let (base, upd_off, upd_pre, delta) = updated?;
    let base_l = fold(&base);
    let upd_pre_l = fold(&upd_pre);

    // Walk IDL layout: own the updated `u64`, frame every other field.
    let mut fresh = 0u32;
    let mut params: Vec<String> = Vec::new();
    let mut ba_params: Vec<String> = Vec::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut post_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    // Owned blob bytes (SPLIT blob): excluded from `setup`, need `< 256` hyps for codecValid.
    let mut owned_blob_offs: Vec<i64> = Vec::new();
    // `< 256` hyps for split blob's owned bytes; `omega` discharges after codecValid simp.
    let mut byte_hyps: Vec<String> = Vec::new();
    // Gap-size hyps `(name, "g.size = len")`: pin offsets so fine atoms land at lift's addresses.
    let mut gap_size_hyps: Vec<(String, String)> = Vec::new();
    let base_raw_blob = base.to_lean();
    let mut updated_seen = false;
    for f in &layout.fields {
        let off = f.offset as i64;
        match &f.kind {
            FieldKind::U64 if off == upd_off => {
                updated_seen = true;
                pre_fields.push(format!("({}, .u64 {})", off, upd_pre_l));
                post_fields.push(format!("({}, .u64 ({} + {}))", off, upd_pre_l, delta));
            }
            FieldKind::Pubkey => {
                let limbs: Vec<String> = (0..4)
                    .map(|_| {
                        let p = format!("o{}", fresh);
                        fresh += 1;
                        params.push(p.clone());
                        p
                    })
                    .collect();
                let rec = format!("⟨{}⟩", limbs.join(", "));
                pre_fields.push(format!("({}, .pubkey {})", off, rec));
                post_fields.push(format!("({}, .pubkey {})", off, rec));
                for (i, limb) in limbs.iter().enumerate() {
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦U64 {})",
                        base_l,
                        off + 8 * i as i64,
                        limb
                    ));
                }
            }
            FieldKind::U64 => {
                let p = format!("fu{}", fresh);
                fresh += 1;
                params.push(p.clone());
                pre_fields.push(format!("({}, .u64 {})", off, p));
                post_fields.push(format!("({}, .u64 {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦U64 {})", base_l, off, p));
            }
            FieldKind::Byte => {
                let p = format!("fb{}", fresh);
                fresh += 1;
                params.push(p.clone());
                pre_fields.push(format!("({}, .byte {})", off, p));
                post_fields.push(format!("({}, .byte {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦ₘ {})", base_l, off, p));
            }
            // Blob field: frame as opaque `↦Bytes` gap unless the lift owns bytes inside it (SPLIT path below).
            FieldKind::Bytes(len) => {
                let len = *len as i64;
                // SPLIT if the lift owns bytes inside [off, off+len); else whole field is one opaque gap.
                let owned: Vec<(i64, String)> = (0..len)
                    .filter_map(|rel| {
                        cell_val(pre, &base_raw_blob, off + rel, true).map(|v| (rel, fold(v)))
                    })
                    .collect();
                if owned.is_empty() {
                    let g = format!("fg{}", fresh);
                    fresh += 1;
                    ba_params.push(g.clone());
                    pre_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    post_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off, g));
                } else {
                    let mut segs: Vec<String> = Vec::new();
                    let mut cursor = 0i64;
                    for (rel, val) in &owned {
                        if *rel > cursor {
                            // Gap before owned byte: pin size (`fg.size = len`) so segsSL places the byte at `base + rel`.
                            let g = format!("fg{}", fresh);
                            fresh += 1;
                            ba_params.push(g.clone());
                            gap_size_hyps.push((
                                format!("h{}_sz", g),
                                format!("{}.size = {}", g, rel - cursor),
                            ));
                            segs.push(format!(".gap {}", g));
                            frame.push(format!(
                                "(effectiveAddr {} {} ↦Bytes {})",
                                base_l,
                                off + cursor,
                                g
                            ));
                        }
                        // Owned byte: NOT framed; fine `.byte` atom matches directly. Needs `< 256` hyp.
                        segs.push(format!(".byte ({})", val));
                        owned_blob_offs.push(off + rel);
                        byte_hyps.push(format!("(h_blob{} : {} < 256)", off + rel, val));
                        cursor = rel + 1;
                    }
                    if cursor < len {
                        // Trailing gap (last seg): no size hyp needed — free ByteArray.
                        let g = format!("fg{}", fresh);
                        fresh += 1;
                        ba_params.push(g.clone());
                        segs.push(format!(".gap {}", g));
                        frame.push(format!(
                            "(effectiveAddr {} {} ↦Bytes {})",
                            base_l,
                            off + cursor,
                            g
                        ));
                    }
                    let seglist = format!("[{}]", segs.join(", "));
                    pre_fields.push(format!("({}, .blob {})", off, seglist));
                    post_fields.push(format!("({}, .blob {})", off, seglist));
                }
            }
        }
    }
    if !updated_seen {
        return None;
    }

    // setup: lift atoms that don't own codec cells (updated u64 + split blob bytes flow through fine form).
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => {
            addr_base.to_lean() == owned_base
                && ((*addr_off == upd_off && matches!(width, Width::Dword))
                    || (matches!(width, Width::Byte) && owned_blob_offs.contains(addr_off)))
        }
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean
        .iter()
        .filter(|a| !is_owned(a))
        .cloned()
        .collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_vault_refinement(VaultRender {
        spec,
        module: &module,
        base_l: &base_l,
        pre_fields: &pre_fields,
        post_fields: &post_fields,
        frame: &frame,
        params: &params,
        ba_params: &ba_params,
        pre,
        post_clean,
        setup_pre: &setup_pre,
        setup_post: &setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        upd_off,
        delta,
        upd_pre_l: &upd_pre_l,
        byte_hyps: &byte_hyps,
        gap_size_hyps: &gap_size_hyps,
    });
    Some((module, lean))
}

struct VaultRender<'a> {
    spec: &'a RefineSpec,
    module: &'a str,
    base_l: &'a str,
    pre_fields: &'a [String],
    post_fields: &'a [String],
    frame: &'a [String],
    params: &'a [String],
    ba_params: &'a [String],
    pre: &'a [Atom],
    post_clean: &'a [Atom],
    setup_pre: &'a [Atom],
    setup_post: &'a [Atom],
    abs_subst: &'a std::collections::BTreeMap<String, String>,
    vars: &'a [String],
    n_cu: usize,
    start_pc: usize,
    exit_pc: usize,
    upd_off: i64,
    delta: i64,
    upd_pre_l: &'a str,
    byte_hyps: &'a [String],
    gap_size_hyps: &'a [(String, String)],
}

/// Render the vault refinement. Proof: `codecCoarse_eq_fine` reshape → simp fine atoms → `sl_exact`.
fn render_vault_refinement(r: VaultRender<'_>) -> String {
    let VaultRender {
        spec,
        module,
        base_l,
        pre_fields,
        post_fields,
        frame,
        params,
        ba_params,
        pre,
        post_clean,
        setup_pre,
        setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        upd_off,
        delta,
        upd_pre_l,
        byte_hyps,
        gap_size_hyps,
    } = r;
    let mut nat_params = vars.join(" ");
    for p in params {
        nat_params.push(' ');
        nat_params.push_str(p);
    }
    // `ensures` corollary binders: only params that appear in the field lists (no unused binders).
    let mut ens_nat = upd_pre_l.to_string();
    for p in params {
        ens_nat.push(' ');
        ens_nat.push_str(p);
    }
    let mut ensures_binders = format!("({ens_nat} : Nat)");
    if !ba_params.is_empty() {
        ensures_binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    // ByteArray group only when a blob field is present; keeps non-blob output byte-identical.
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    for h in byte_hyps {
        binders.push_str(&format!("\n    {}", h));
    }
    for (name, prop) in gap_size_hyps {
        binders.push_str(&format!("\n    ({} : {})", name, prop));
    }
    // Simp sets: conditioned on field kinds present to avoid `unusedSimpArgs` and keep non-blob output stable.
    let has_pubkey = pre_fields.iter().any(|f| f.contains(".pubkey"));
    let has_blob = !ba_params.is_empty();
    let mut fine: Vec<String> = vec!["codecFine".into(), "FieldVal.fine".into()];
    if has_pubkey {
        fine.push("pubkeyIs".into());
    }
    if has_blob {
        fine.push("segsSL".into());
        fine.push("FieldSeg.sl".into());
    }
    // SPLIT blob: add `FieldSeg.size` + gap-size hyps so running offsets reduce to concrete addresses.
    if !gap_size_hyps.is_empty() {
        fine.push("FieldSeg.size".into());
        for (name, _) in gap_size_hyps {
            fine.push(name.clone());
        }
    }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob {
        valid.push("segsValid");
        valid.push("FieldSeg.valid");
    }
    let valid_simp = valid.join(", ");
    // SPLIT blob: `(v % 256) < 256` residual after codecValid simp → `omega`; whole-gap closes in simp alone.
    let valid_tac = if byte_hyps.is_empty() {
        format!("by simp [{valid_simp}]")
    } else {
        format!("by simp [{valid_simp}] <;> omega")
    };
    let pre_list = pre_fields.join(", ");
    let post_list = post_fields.join(", ");
    let frame_s = frame.join(" **\n      ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
        "/-
  {pred} asm-refines theorem for a multi-field NON-token account.
  MECHANICALLY EMITTED by qedlift from the Codama IDL account layout +
  the lift's atoms. The lift owns the updated `u64` field; the account
  codec is reshaped coarse→fine via the layout-general `account_agg`
  (`codecCoarse_eq_fine`) and the untouched fields are framed.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    {binders}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {base}
      [{pre_list}]
      [{post_list}]
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  rw [codecCoarse_eq_fine {base}
        [{pre_list}]
        ({valid_tac}),
      codecCoarse_eq_fine {base}
        [{post_list}]
        ({valid_tac})]
  simp only [{fine_simp}]
  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  sl_exact framed

/-- qedgen `ensures`-shape, mechanically discharged: the mutated `u64`
    field (offset {upd_off}) shifts by {delta}. Pairs with `refines_asm`
    (which says the bytecode realises this field-list transition); together
    they discharge qedgen's `accessor post = accessor pre ± k` over the
    decoded field list via the layout-general accessor projection. -/
theorem ensures
    {ensures_binders} :
    u64FieldAt {upd_off} [{post_list}]
      = u64FieldAt {upd_off} [{pre_list}] + {delta} := by
  qedsvm_discharge

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        binders = binders,
        ensures_binders = ensures_binders,
        upd_off = upd_off,
        delta = delta,
        valid_tac = valid_tac,
        fine_simp = fine_simp,
        n = n_cu,
        entry = start_pc,
        exit = exit_pc,
        lift_pre = lift_pre,
        lift_post = lift_post,
        base = base_l,
        pre_list = pre_list,
        post_list = post_list,
        setup_pre = setup_pre_s,
        setup_post = setup_post_s,
        frame = frame_s,
    )
}

// ════════════════════════════════════════════════════════════════
// Spec-driven descriptor path (prototype) — the seam to qedspec.
//
// Same machinery as `emit_vault_refinement` (layout-general `AsmRefinesFieldUpdate`,
// reshape via `account_agg`/`codecCoarse_eq_fine`, frame the untouched fields), but
// the layout + mutated field + delta come from a qedgen-shaped `RefinementDescriptor`
// instead of the hardcoded `refine_registry` arm match and the role-keyed
// `resolve_layout(..., "vault")`. This is what closes the "describe properties →
// prove the bytes" loop: a new program costs a descriptor, not a Rust edit.
//
// Differences from `emit_vault_refinement`, all additive (no change to the registry
// path, so existing pins stay byte-identical):
//   - predicate is always `AsmRefinesFieldUpdate` (no registry lookup);
//   - the layout is the descriptor's, validated against the lift (the bytes must
//     mutate the field the descriptor names — a real soundness check);
//   - the single-field case (empty frame, e.g. the counter) is handled: no
//     `cuTripleWithinMem_frame_right`, just `sl_exact lift`.
//   - split-blob (owned bytes inside a `bytes` field) is not handled here; a `bytes`
//     field is framed whole as one opaque gap (covers counter + vault).
// ════════════════════════════════════════════════════════════════

pub(super) fn emit_descriptor_refinement(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
) -> Option<(String, String)> {
    // Shape substrate: when the descriptor has no inline layout, its account's
    // layout is resolved from `ctx.idl`/`ctx.sidecar_layouts` — the SAME
    // `qed-analysis` path the registry lift uses, so the seam stays name-level
    // (offsets are the IDL's job, not the descriptor's).
    let RefinementCtx {
        lift_module,
        pre,
        post: post_clean,
        abs_subst,
        idl,
        sidecar_layouts,
        ..
    } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // Shape: inline layout (no-IDL fallback) or resolved from the IDL by account name.
    let layout = match desc.explicit_layout() {
        Some(l) => l,
        None => match resolve_layout(sidecar_layouts, idl, &desc.account) {
            Some(l) => l,
            None => {
                eprintln!(
                    "descriptor: no inline layout and could not resolve account {:?} from \
                     the IDL; skipping refinement",
                    desc.account
                );
                return None;
            }
        },
    };
    // Mutated field's offset comes from the resolved layout (name-level seam).
    let mutated_off = match layout.fields.iter().find(|f| f.name == desc.mutated) {
        Some(f) => f.offset as i64,
        None => {
            eprintln!(
                "descriptor: mutated field {:?} is not in the resolved layout for {:?}; \
                 skipping refinement",
                desc.mutated, desc.account
            );
            return None;
        }
    };

    // Determine the mutated cell and the delta expression, by op kind. `delta_expr` is what
    // the field is credited by, rendered as Lean: a literal `k` (add_const) or the
    // parameter's binder name (add_param). `param_binder` is Some only for a parameter
    // delta — it is a lift binder that must also appear in the standalone `ensures` theorem.
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    // Folded Lean value of the Dword cell at (base, off) in the pre — used to tell the
    // mutated field's own pre-value apart from the parameter operand in `field += param`.
    let pre_dword_val = |b: &str, off: i64| -> Option<String> {
        pre.iter().find_map(|a| match a {
            Atom::Mem {
                addr_base,
                addr_off,
                width,
                value,
                ..
            } if addr_base.to_lean() == b && *addr_off == off && matches!(width, Width::Dword) => {
                Some(fold(value))
            }
            _ => None,
        })
    };

    let base: Expr;
    let upd_off: i64;
    let upd_pre: Expr;
    let delta_expr: String;
    let param_binder: Option<String>;

    match &desc.op {
        DescriptorOp::AddConst { add_const } => {
            // Positive constant deltas: `+1` cleans via `wrapAdd_one_of_lt`, any other
            // positive literal via `wrapAdd_const_of_lt`. Zero / negative are out of scope.
            if *add_const < 1 {
                eprintln!(
                    "descriptor: only a positive constant op.add_const is wired (got {}); \
                     skipping refinement",
                    add_const
                );
                return None;
            }
            // The updated `u64` cell: `NatAdd(InitMem, Const)`.
            let mut found: Option<(Expr, i64, Expr, i64)> = None;
            for atom in post_clean {
                if let Atom::Mem {
                    addr_base,
                    addr_off,
                    width,
                    value,
                    ..
                } = atom
                {
                    if matches!(width, Width::Dword) {
                        if let Expr::NatAdd(a, b) = value {
                            if let (Expr::InitMem(_), Expr::Const(k)) = (a.as_ref(), b.as_ref()) {
                                found = Some(((*addr_base).clone(), *addr_off, (**a).clone(), *k));
                                break;
                            }
                        }
                    }
                }
            }
            let (b, off, pre_e, k) = found?;
            // Soundness: the bytes' delta must match the descriptor's claimed constant.
            if k != *add_const {
                eprintln!(
                    "descriptor: op claims +{} but the lift increments the field by {}; \
                     refusing to emit a refinement that misdescribes the bytes",
                    add_const, k
                );
                return None;
            }
            base = b;
            upd_off = off;
            upd_pre = pre_e;
            delta_expr = k.to_string();
            param_binder = None;
        }
        DescriptorOp::AddParam { add_param } => {
            // The updated cell is `field += param`: `NatAdd(InitMem_field, InitMem_param)`,
            // where one operand is the cell's own pre-value and the other is a distinct
            // runtime read. Inline first-cut: the param is matched as that other read; the
            // IDL instruction-args resolution that pins `add_param` to a serialized offset
            // is a follow-on (so this labels, but does not yet verify, the param's identity).
            let mut found: Option<(Expr, i64, Expr, String)> = None;
            for atom in post_clean {
                if let Atom::Mem {
                    addr_base,
                    addr_off,
                    width,
                    value,
                    ..
                } = atom
                {
                    if !matches!(width, Width::Dword) {
                        continue;
                    }
                    if let Expr::NatAdd(a, b) = value {
                        if !(is_initmem(a) && is_initmem(b)) {
                            continue;
                        }
                        let bl = addr_base.to_lean();
                        let pre_val = match pre_dword_val(&bl, *addr_off) {
                            Some(v) => v,
                            None => continue,
                        };
                        let (a_l, b_l) = (fold(a), fold(b));
                        let (field_e, param_l) = if a_l == pre_val {
                            ((**a).clone(), b_l)
                        } else if b_l == pre_val {
                            ((**b).clone(), a_l)
                        } else {
                            continue;
                        };
                        found = Some(((*addr_base).clone(), *addr_off, field_e, param_l));
                        break;
                    }
                }
            }
            let (b, off, pre_e, param_l) = match found {
                Some(t) => t,
                None => {
                    eprintln!(
                        "descriptor: op.add_param {:?} but the lift has no `field += <runtime \
                         read>` cell; skipping refinement",
                        add_param
                    );
                    return None;
                }
            };
            base = b;
            upd_off = off;
            upd_pre = pre_e;
            delta_expr = param_l.clone();
            param_binder = Some(param_l);
        }
    }

    // Soundness: the bytes must mutate the field the descriptor names.
    if upd_off != mutated_off {
        eprintln!(
            "descriptor: field {:?} is at offset {} but the lift mutates offset {}; \
             refusing to emit a refinement that misdescribes the bytes",
            desc.mutated, mutated_off, upd_off
        );
        return None;
    }

    let base_l = fold(&base);
    let upd_pre_l = fold(&upd_pre);

    // Walk the descriptor layout: own the updated `u64`, frame every other field.
    let mut fresh = 0u32;
    let mut params: Vec<String> = Vec::new();
    let mut ba_params: Vec<String> = Vec::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut post_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    let mut updated_seen = false;
    for f in &layout.fields {
        let off = f.offset as i64;
        match &f.kind {
            FieldKind::U64 if off == upd_off => {
                updated_seen = true;
                pre_fields.push(format!("({}, .u64 {})", off, upd_pre_l));
                post_fields.push(format!("({}, .u64 ({} + {}))", off, upd_pre_l, delta_expr));
            }
            FieldKind::Pubkey => {
                let limbs: Vec<String> = (0..4)
                    .map(|_| {
                        let p = format!("o{}", fresh);
                        fresh += 1;
                        params.push(p.clone());
                        p
                    })
                    .collect();
                let rec = format!("⟨{}⟩", limbs.join(", "));
                pre_fields.push(format!("({}, .pubkey {})", off, rec));
                post_fields.push(format!("({}, .pubkey {})", off, rec));
                for (i, limb) in limbs.iter().enumerate() {
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦U64 {})",
                        base_l,
                        off + 8 * i as i64,
                        limb
                    ));
                }
            }
            FieldKind::U64 => {
                let p = format!("fu{}", fresh);
                fresh += 1;
                params.push(p.clone());
                pre_fields.push(format!("({}, .u64 {})", off, p));
                post_fields.push(format!("({}, .u64 {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦U64 {})", base_l, off, p));
            }
            FieldKind::Byte => {
                let p = format!("fb{}", fresh);
                fresh += 1;
                params.push(p.clone());
                pre_fields.push(format!("({}, .byte {})", off, p));
                post_fields.push(format!("({}, .byte {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦ₘ {})", base_l, off, p));
            }
            // Opaque region: framed whole as one gap (no split-blob in the prototype).
            FieldKind::Bytes(_) => {
                let g = format!("fg{}", fresh);
                fresh += 1;
                ba_params.push(g.clone());
                pre_fields.push(format!("({}, .blob [.gap {}])", off, g));
                post_fields.push(format!("({}, .blob [.gap {}])", off, g));
                frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off, g));
            }
        }
    }
    if !updated_seen {
        return None;
    }

    // setup: lift atoms that don't own the updated `u64` (it flows through the fine codec).
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => {
            addr_base.to_lean() == owned_base
                && *addr_off == upd_off
                && matches!(width, Width::Dword)
        }
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean
        .iter()
        .filter(|a| !is_owned(a))
        .cloned()
        .collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_descriptor_refinement(
        desc,
        &module,
        ctx,
        &DescriptorRender {
            base_l: &base_l,
            pre_fields: &pre_fields,
            post_fields: &post_fields,
            frame: &frame,
            params: &params,
            ba_params: &ba_params,
            setup_pre: &setup_pre,
            setup_post: &setup_post,
            upd_off,
            delta_expr: &delta_expr,
            param_binder: param_binder.as_deref(),
            upd_pre_l: &upd_pre_l,
        },
    );
    Some((module, lean))
}

/// The field-walk products `emit_descriptor_refinement` hands its renderer.
struct DescriptorRender<'a> {
    base_l: &'a str,
    pre_fields: &'a [String],
    post_fields: &'a [String],
    frame: &'a [String],
    params: &'a [String],
    ba_params: &'a [String],
    setup_pre: &'a [Atom],
    setup_post: &'a [Atom],
    upd_off: i64,
    delta_expr: &'a str,
    param_binder: Option<&'a str>,
    upd_pre_l: &'a str,
}

fn render_descriptor_refinement(
    desc: &RefinementDescriptor,
    module: &str,
    ctx: RefinementCtx<'_>,
    r: &DescriptorRender<'_>,
) -> String {
    let RefinementCtx {
        pre,
        post: post_clean,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        ..
    } = ctx;
    let &DescriptorRender {
        base_l,
        pre_fields,
        post_fields,
        frame,
        params,
        ba_params,
        setup_pre,
        setup_post,
        upd_off,
        delta_expr,
        param_binder,
        upd_pre_l,
    } = r;
    let mut nat_params = vars.join(" ");
    for p in params {
        nat_params.push(' ');
        nat_params.push_str(p);
    }
    // `ensures` corollary binders: the field-list params, plus the runtime parameter binder
    // for a parameter delta (the const case adds none).
    let mut ens_nat = upd_pre_l.to_string();
    for p in params {
        ens_nat.push(' ');
        ens_nat.push_str(p);
    }
    if let Some(pb) = param_binder {
        ens_nat.push(' ');
        ens_nat.push_str(pb);
    }
    let mut ensures_binders = format!("({ens_nat} : Nat)");
    if !ba_params.is_empty() {
        ensures_binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }

    let has_pubkey = pre_fields.iter().any(|f| f.contains(".pubkey"));
    let has_blob = !ba_params.is_empty();
    let mut fine: Vec<String> = vec!["codecFine".into(), "FieldVal.fine".into()];
    if has_pubkey {
        fine.push("pubkeyIs".into());
    }
    if has_blob {
        fine.push("segsSL".into());
        fine.push("FieldSeg.sl".into());
    }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob {
        valid.push("segsValid");
        valid.push("FieldSeg.valid");
    }
    let valid_tac = format!("by simp [{}]", valid.join(", "));

    let pre_list = pre_fields.join(", ");
    let post_list = post_fields.join(", ");
    let frame_s = frame.join(" **\n      ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);
    let handler_clause = desc
        .handler
        .as_ref()
        .map(|h| format!(", handler {}", h))
        .unwrap_or_default();

    // Single-field account (empty frame, e.g. the counter): no `frame_right`,
    // the reshaped fine codec IS the lift's owned cell, so `sl_exact lift`.
    let proof_tail = if frame.is_empty() {
        "  sl_exact lift".to_string()
    } else {
        format!(
            "  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  sl_exact framed",
            frame = frame_s
        )
    };

    format!(
        "/-
  AsmRefinesFieldUpdate asm-refines theorem, SPEC-DRIVEN. Emitted by qedlift
  from a qedspec-shaped refinement descriptor (account {account}{handler},
  mutated field {mutated}), NOT from the hardcoded `refine_registry`. The
  field offsets come from the IDL (the shape substrate), not the descriptor.
  The lift owns the updated `u64` field; the account codec is reshaped
  coarse→fine via the layout-general `account_agg` (`codecCoarse_eq_fine`)
  and the untouched fields (if any) are framed. See docs/DEVEX_QEDSPEC_GAP.md.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    {binders}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.AsmRefinesFieldUpdate cr {n} 0 {entry} {exit} rr {base}
      [{pre_list}]
      [{post_list}]
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.AsmRefinesFieldUpdate
  rw [codecCoarse_eq_fine {base}
        [{pre_list}]
        ({valid_tac}),
      codecCoarse_eq_fine {base}
        [{post_list}]
        ({valid_tac})]
  simp only [{fine_simp}]
{proof_tail}

/-- qedgen `ensures`-shape, mechanically discharged: the mutated `u64`
    field (offset {upd_off}) shifts by {delta}. Pairs with `refines_asm`
    (which says the bytecode realises this field-list transition); together
    they discharge qedgen's `accessor post = accessor pre ± k` over the
    decoded field list via the layout-general accessor projection. -/
theorem ensures
    {ensures_binders} :
    u64FieldAt {upd_off} [{post_list}]
      = u64FieldAt {upd_off} [{pre_list}] + {delta} := by
  qedsvm_discharge

end Examples.{module}
",
        account = desc.account,
        handler = handler_clause,
        mutated = desc.mutated,
        lift = strip_refinement(module),
        module = module,
        binders = binders,
        ensures_binders = ensures_binders,
        upd_off = upd_off,
        delta = delta_expr,
        valid_tac = valid_tac,
        fine_simp = fine_simp,
        n = n_cu,
        entry = start_pc,
        exit = exit_pc,
        lift_pre = lift_pre,
        lift_post = lift_post,
        base = base_l,
        pre_list = pre_list,
        post_list = post_list,
        setup_pre = setup_pre_s,
        setup_post = setup_post_s,
        proof_tail = proof_tail,
    )
}

/// "PTokenMintToRefinement" → "PTokenMintTo".
fn strip_refinement(module: &str) -> String {
    module
        .strip_suffix("Refinement")
        .unwrap_or(module)
        .to_string()
}
