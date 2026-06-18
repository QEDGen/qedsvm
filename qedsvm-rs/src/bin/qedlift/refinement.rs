use qed_analysis::layout::{AccountLayout, FieldKind};

use super::aggregation::{render_mint_agg_module, render_token_agg_module};
use super::core::{Atom, Expr, Width};
use super::emit::{atoms_to_lean, fold_abstractions};
use super::input::{resolve_layout, RefinementDescriptor};

// ════════════════════════════════════════════════════════════════
// Refinement codegen — mechanically emit the per-arm `AsmRefines…` obligation theorem.
// Detects mutated cells, classifies codec (token/mint/counter/vault), picks aggregation lemma.
// Returns `(module_name, lean)` or `None` for unregistered arms / unrecognized layouts.
// ════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, PartialEq, Eq)]
enum CodecKind { Token, Mint, Counter, Vault }

struct RefineSpec {
    asm_pred: &'static str,
    /// account roles in `AsmRefines…` argument order.
    accounts: &'static [(&'static str, CodecKind)],
}

fn refine_registry(arm: &str) -> Option<RefineSpec> {
    match arm {
        "Transfer" | "TransferChecked" => Some(RefineSpec {
            asm_pred: "AsmRefinesTokenTransfer",
            accounts: &[("src", CodecKind::Token), ("dst", CodecKind::Token)],
        }),
        "MintTo" => Some(RefineSpec {
            asm_pred: "AsmRefinesTokenMintTo",
            accounts: &[("mint", CodecKind::Mint), ("dest", CodecKind::Token)],
        }),
        "Burn" => Some(RefineSpec {
            asm_pred: "AsmRefinesTokenBurn",
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
        s.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Counter | CodecKind::Vault))
    })
}

/// Value of a memory cell at `(base_raw, off)` with the given byte-ness,
/// if the lift owns it.
fn cell_val<'a>(atoms: &'a [Atom], base_raw: &str, off: i64, byte: bool) -> Option<&'a Expr> {
    for a in atoms {
        if let Atom::Mem { addr_base, addr_off, width, value, .. } = a {
            if *addr_off == off && matches!(width, Width::Byte) == byte
               && addr_base.to_lean() == base_raw {
                return Some(value);
            }
        }
    }
    None
}

/// A balance/supply cell mutated in the post (`a ± b`, both loaded).
struct MutCell { base: Expr, base_raw: String, off: i64, a: Expr, b: Expr, is_sub: bool }

struct AcctBuild {
    base_arg: String,                  // "(addr5 + 88)" — lemma base argument
    record: String,                    // the codec record literal
    rw_pre: String,                    // aggregation rw call at the pre value
    rw_post: String,                   // aggregation rw call at the post value
    frame: Vec<String>,                // frame atoms
    owned: Vec<(String, i64, bool)>,   // lift cells consumed (excluded from setup)
    params: Vec<String>,               // new Nat params (framed owner o…)
    barrays: Vec<String>,              // new ByteArray params
    hyps: Vec<String>,                 // size + byte-bound hypotheses
    // Token aggregation: (lemma_name, owner_owned, rest_pattern). `None` for mint (hand-written).
    agg: Option<(String, bool, Vec<i64>)>,
    // `codecCoarse base (tokenFields/mintFields …)` atoms for pre and post. The keystone
    // (`tokenAcctBalance_codec`/`mintSupply_codec`) equates the bespoke atom to these, reshaping
    // the `AsmRefinesToken*` obligation to the layout-general `refines_field` corollary.
    field_pre: String,
    field_post: String,
}

pub(super) fn emit_refinement(
    arm_name:     &str,
    lift_module:  &str,
    pre:          &[Atom],
    post_clean:   &[Atom],
    abs_subst:    &std::collections::BTreeMap<String, String>,
    vars:         &[String],
    n_cu:         usize,
    start_pc:     usize,
    exit_pc:      usize,
    idl:          Option<&serde_json::Value>,
    // qedrecover-emitted layouts; preferred over `idl` for account-codec offsets (#41 loop closure).
    sidecar_layouts: Option<&[AccountLayout]>,
    // Returns `(refine_module, refine_lean, optional (agg_module, agg_lean))`.
) -> Option<(String, String, Option<(String, String)>)> {
    let spec = refine_registry(arm_name)?;

    // Counter codec (single u64, coarse=fine): dedicated path keeps token/mint codegen byte-identical.
    if spec.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Counter)) {
        return emit_counter_refinement(&spec, lift_module, pre, post_clean,
            abs_subst, vars, n_cu, start_pc, exit_pc);
    }

    // Vault codec (IDL layout, multi-field): owns updated u64, frames the rest, reshapes via `account_agg`.
    if spec.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Vault)) {
        return emit_vault_refinement(&spec, lift_module, pre, post_clean,
            abs_subst, vars, n_cu, start_pc, exit_pc, idl, sidecar_layouts);
    }

    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // ── Detect mutated account cells (a ± b, both InitMem) ──────────
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    let mut muts: Vec<MutCell> = Vec::new();
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, value, .. } = atom {
            let (a, b, is_sub) = match value {
                Expr::CleanSub(a, b) => ((**a).clone(), (**b).clone(), true),
                Expr::NatAdd(a, b)   => ((**a).clone(), (**b).clone(), false),
                _ => continue,
            };
            if is_initmem(&a) && is_initmem(&b) {
                muts.push(MutCell { base: addr_base.clone(), base_raw: addr_base.to_lean(),
                    off: *addr_off, a, b, is_sub });
            }
        }
    }
    if muts.is_empty() { return None; }
    // The transferred amount `b` is shared across all mutated cells.
    let amount = fold(&muts[0].b);

    // ── Assign each registry account to a mutated cell ─────────────────────────────────────────
    // Token amount cells have a mint dword at off-64; mint supply cells have is_initialized at off+9.
    let is_mint_mut = |m: &MutCell| cell_val(pre, &m.base_raw, m.off + 9, true).is_some();
    let is_tok_mut  = |m: &MutCell| cell_val(pre, &m.base_raw, m.off - 64, false).is_some();
    let mut used = vec![false; muts.len()];
    let mut builds: Vec<AcctBuild> = Vec::new();
    let mut barray_ctr = 0u32;
    let mut framed_owner = false;
    for (role, codec) in spec.accounts {
        // Pick unused mutated cell for this codec; for two token accounts (Transfer), src=sub, dst=add.
        let want_sub = *role == "src" || *role == "account";
        let idx = (0..muts.len()).find(|&i| {
            !used[i] && match codec {
                CodecKind::Token => is_tok_mut(&muts[i])
                    && (spec.accounts.iter().filter(|(_, c)| *c == CodecKind::Token).count() < 2
                        || muts[i].is_sub == want_sub),
                CodecKind::Mint => is_mint_mut(&muts[i]),
                // All-counter / all-vault specs take their early
                // `emit_*_refinement` paths; this loop only runs for
                // token/mint codecs.
                CodecKind::Counter | CodecKind::Vault =>
                    unreachable!("counter/vault codec handled by its own emitter"),
            }
        })?;
        used[idx] = true;
        let m = &muts[idx];
        let field_off = if *codec == CodecKind::Token { 64 } else { 36 };
        let base_off = m.off - field_off;
        let base_expr = fold(&m.base);
        let base_arg = format!("({} + {})", base_expr, base_off);
        let build = match codec {
            CodecKind::Token => build_token(pre, m, &base_expr, base_off, &amount,
                &fold, &mut barray_ctr, &mut framed_owner)?,
            CodecKind::Mint  => build_mint(pre, m, &base_expr, base_off, &amount,
                &fold, &mut barray_ctr)?,
            CodecKind::Counter | CodecKind::Vault =>
                unreachable!("counter/vault codec handled by its own emitter"),
        };
        let _ = base_arg;
        builds.push(build);
    }

    // ── Assemble setup atoms (lift cells not owned by any account) ──
    let owned: std::collections::HashSet<(String, i64, bool)> =
        builds.iter().flat_map(|b| b.owned.iter().cloned()).collect();
    let is_owned = |a: &Atom| match a {
        Atom::Mem { addr_base, addr_off, width, .. } =>
            owned.contains(&(addr_base.to_lean(), *addr_off, matches!(width, Width::Byte))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    // ── Render ──────────────────────────────────────────────────────
    let module = format!("{}Refinement", lift_module);
    let lean = render_refinement(&spec, &module, &builds, pre, post_clean,
        &setup_pre, &setup_post, abs_subst, vars, &amount, n_cu, start_pc, exit_pc);

    // Emit aggregation module from detected owned-byte patterns. Token -> `PToken.TransferAggregation`;
    // mint -> `PToken.MintAggregation`. Rest-region start/size from IDL; fallback = SPL token 72/165.
    let (tok_rest_start, tok_size) = resolve_layout(sidecar_layouts, idl, "token")
        .and_then(|l| {
            let amount = l.fields.iter().find(|f| f.name == "amount")?;
            Some((amount.offset as i64 + 8, l.size as i64))
        })
        .unwrap_or((72, 165));

    let uses_mint = spec.accounts.iter().any(|(_, c)| matches!(c, CodecKind::Mint));
    let aggregation = if uses_mint {
        // Mint codec: supply/rest offsets from the IDL mint layout; fallback = SPL defaults.
        let (supply_off, rest_off, mint_size) = resolve_layout(sidecar_layouts, idl, "mint")
            .and_then(|l| {
                let s = l.fields.iter().find(|f| f.name == "supply")?;
                Some((s.offset as i64, s.offset as i64 + 8, l.size as i64))
            })
            .unwrap_or((36, 44, 82));
        let agg_lean = render_mint_agg_module(
            "Examples.PTokenMintAggregation", supply_off, rest_off, mint_size,
            tok_rest_start, tok_size);
        Some(("PToken.MintAggregation".to_string(), agg_lean))
    } else {
        let token_aggs: Vec<(&str, bool, Vec<i64>)> = builds.iter()
            .filter_map(|b| b.agg.as_ref().map(|(n, oo, p)| (n.as_str(), *oo, p.clone())))
            .collect();
        if token_aggs.is_empty() {
            None
        } else {
            let agg_lean = render_token_agg_module(
                "Examples.PTokenTransferAggregation", &token_aggs, tok_rest_start, tok_size);
            Some(("PToken.TransferAggregation".to_string(), agg_lean))
        }
    };
    Some((module, lean, aggregation))
}

/// Build a token-account aggregation (src/dst/dest patterns).
fn build_token(
    pre: &[Atom], m: &MutCell, base_expr: &str, base_off: i64, amount: &str,
    fold: &dyn Fn(&Expr) -> String, barray_ctr: &mut u32, framed_owner: &mut bool,
) -> Option<AcctBuild> {
    let base_arg = format!("({} + {})", base_expr, base_off);
    let mut owned = Vec::new();
    let mut params = Vec::new();
    let mut barrays = Vec::new();
    let mut hyps = Vec::new();
    let mut frame = Vec::new();

    let mut mint = Vec::new();
    for i in 0..4 {
        let off = base_off + 8 * i;
        let v = fold(cell_val(pre, &m.base_raw, off, false)?);
        mint.push(v);
        owned.push((m.base_raw.clone(), off, false));
    }
    let owner_owned = cell_val(pre, &m.base_raw, base_off + 32, false).is_some();
    let owner: Vec<String> = if owner_owned {
        (0..4).map(|i| {
            let off = base_off + 32 + 8 * i;
            owned.push((m.base_raw.clone(), off, false));
            fold(cell_val(pre, &m.base_raw, off, false).unwrap())
        }).collect()
    } else {
        if *framed_owner { return None; } // only one framed-owner account supported
        *framed_owner = true;
        for i in 0..4 {
            params.push(format!("o{}", i));
            frame.push(format!("(effectiveAddr {} {} ↦U64 o{})", base_expr, base_off + 32 + 8 * i, i));
        }
        (0..4).map(|i| format!("o{}", i)).collect()
    };
    let amt_field = fold(&m.a);
    owned.push((m.base_raw.clone(), base_off + 64, false));

    // rest bytes owned in [base+72, base+165).
    let mut rest_bytes: Vec<i64> = Vec::new();
    for a in pre {
        if let Atom::Mem { addr_base, addr_off, width, .. } = a {
            if addr_base.to_lean() == m.base_raw && matches!(width, Width::Byte)
               && *addr_off >= base_off + 72 && *addr_off < base_off + 165 {
                rest_bytes.push(*addr_off - base_off);
            }
        }
    }
    rest_bytes.sort();
    let byte_val = |off: i64| fold(cell_val(pre, &m.base_raw, base_off + off, true).unwrap());
    let g1 = { *barray_ctr += 1; format!("g{}", *barray_ctr) };
    let g2 = { *barray_ctr += 1; format!("g{}", *barray_ctr) };
    barrays.push(g1.clone()); barrays.push(g2.clone());

    let hb = |v: &str| format!("h_{}", v);
    let g1sz = format!("{}sz", g1);
    // (lemma, rest-record, rw_args_tail) — tail is lemma args after base/mint/owner/amount.
    let (lemma, rest, rest_args): (&str, String, String) = match rest_bytes.as_slice() {
        [72, 108, 109] => {
            let (b72, b108, b109) = (byte_val(72), byte_val(108), byte_val(109));
            for o in [72, 108, 109] { owned.push((m.base_raw.clone(), base_off + o, true)); }
            hyps.push(format!("({} : {}.size = 35)", g1sz, g1));
            hyps.push(format!("({} : {} < 256)", hb(&b72), b72));
            hyps.push(format!("({} : {} < 256)", hb(&b108), b108));
            hyps.push(format!("({} : {} < 256)", hb(&b109), b109));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 73, g1));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 110, g2));
            ("src_account_eq",
             format!("PartialState.byteBA {} ++ ({} ++ (PartialState.byteBA {} ++ (PartialState.byteBA {} ++ {})))", b72, g1, b108, b109, g2),
             format!("{} {} {} {} {} {} {} {} {}", b72, b108, b109, g1, g2, g1sz, hb(&b72), hb(&b108), hb(&b109)))
        }
        [108] => {
            let b108 = byte_val(108);
            owned.push((m.base_raw.clone(), base_off + 108, true));
            hyps.push(format!("({} : {}.size = 36)", g1sz, g1));
            hyps.push(format!("({} : {} < 256)", hb(&b108), b108));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 72, g1));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 109, g2));
            ("dst_account_eq",
             format!("{} ++ (PartialState.byteBA {} ++ {})", g1, b108, g2),
             format!("{} {} {} {} {}", b108, g1, g2, g1sz, hb(&b108)))
        }
        [108, 109] => {
            let (b108, b109) = (byte_val(108), byte_val(109));
            for o in [108, 109] { owned.push((m.base_raw.clone(), base_off + o, true)); }
            hyps.push(format!("({} : {}.size = 36)", g1sz, g1));
            hyps.push(format!("({} : {} < 256)", hb(&b108), b108));
            hyps.push(format!("({} : {} < 256)", hb(&b109), b109));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 72, g1));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 110, g2));
            ("dest_account_eq",
             format!("{} ++ (PartialState.byteBA {} ++ (PartialState.byteBA {} ++ {}))", g1, b108, b109, g2),
             format!("{} {} {} {} {} {} {}", b108, b109, g1, g2, g1sz, hb(&b108), hb(&b109)))
        }
        _ => return None,
    };

    let owner_args = owner.join(" ");
    let mint_args = mint.join(" ");
    let record = format!(
        "{{ mint := ⟨{}⟩,\n        owner := ⟨{}⟩, amount := {},\n        rest := {} }}",
        mint.join(", "), owner.join(", "), amt_field, rest);
    let post_amt = if m.is_sub { format!("({} - {})", amt_field, amount) } else { format!("({} + {})", amt_field, amount) };
    let rw_pre = format!("{} {} {} {} {} {}", lemma, base_arg, mint_args, owner_args, amt_field, rest_args);
    let rw_post = format!("{} {} {} {} {} {}", lemma, base_arg, mint_args, owner_args, post_amt, rest_args);
    let agg = Some((lemma.to_string(), owner_owned, rest_bytes.clone()));
    // codecCoarse field list (SPL token layout) — `tokenAcctBalance_codec` keystone target.
    let field_pre = format!(
        "codecCoarse {} (SVM.Solana.tokenFields ⟨{}⟩ ⟨{}⟩ {} ({}))",
        base_arg, mint.join(", "), owner.join(", "), amt_field, rest);
    let field_post = format!(
        "codecCoarse {} (SVM.Solana.tokenFields ⟨{}⟩ ⟨{}⟩ {} ({}))",
        base_arg, mint.join(", "), owner.join(", "), post_amt, rest);
    Some(AcctBuild { base_arg, record, rw_pre, rw_post, frame, owned, params, barrays, hyps, agg,
        field_pre, field_post })
}

/// Build a mint-account aggregation (full preAuth or supply-only).
fn build_mint(
    pre: &[Atom], m: &MutCell, base_expr: &str, base_off: i64, amount: &str,
    fold: &dyn Fn(&Expr) -> String, barray_ctr: &mut u32,
) -> Option<AcctBuild> {
    let base_arg = format!("({} + {})", base_expr, base_off);
    let mut owned = Vec::new();
    let mut barrays = Vec::new();
    let mut hyps = Vec::new();
    let mut frame = Vec::new();

    let supply = fold(&m.a);
    owned.push((m.base_raw.clone(), base_off + 36, false));
    let b45 = fold(cell_val(pre, &m.base_raw, base_off + 45, true)?);
    owned.push((m.base_raw.clone(), base_off + 45, true));
    hyps.push(format!("(h_{} : {} < 256)", b45, b45));

    let g_rest = { *barray_ctr += 1; format!("g{}", *barray_ctr) }; // gD (1B)
    let g_free = { *barray_ctr += 1; format!("g{}", *barray_ctr) }; // gF (36B)
    barrays.push(g_rest.clone()); barrays.push(g_free.clone());
    hyps.push(format!("({}sz : {}.size = 1)", g_rest, g_rest));
    frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 44, g_rest));
    frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 46, g_free));
    let rest = format!("{} ++ (PartialState.byteBA {} ++ {})", g_rest, b45, g_free);

    let preauth_owned = cell_val(pre, &m.base_raw, base_off + 4, false).is_some();
    let (lemma, preauth, pre_args): (&str, String, String) = if preauth_owned {
        let b0 = fold(cell_val(pre, &m.base_raw, base_off, true)?);
        owned.push((m.base_raw.clone(), base_off, true));
        hyps.insert(0, format!("(h_{} : {} < 256)", b0, b0));
        let mut ps = Vec::new();
        for i in 0..4 {
            let off = base_off + 4 + 8 * i;
            ps.push(fold(cell_val(pre, &m.base_raw, off, false)?));
            owned.push((m.base_raw.clone(), off, false));
        }
        let g_a = { *barray_ctr += 1; format!("g{}", *barray_ctr) }; // gA (3B)
        barrays.insert(0, g_a.clone());
        hyps.insert(0, format!("({}sz : {}.size = 3)", g_a, g_a));
        frame.insert(0, format!("memBytesIs ({} + {}) {}", base_expr, base_off + 1, g_a));
        ("mint_account_eq",
         format!("PartialState.byteBA {} ++ ({} ++ (PartialState.u64LE {} ++ (PartialState.u64LE {} ++ (PartialState.u64LE {} ++ PartialState.u64LE {}))))",
            b0, g_a, ps[0], ps[1], ps[2], ps[3]),
         format!("{} {} {} {} {} {}", b0, ps[0], ps[1], ps[2], ps[3], format!("{}", b45)))
    } else {
        let pa = { *barray_ctr += 1; format!("preAuth{}", *barray_ctr) };
        barrays.insert(0, pa.clone());
        frame.insert(0, format!("memBytesIs ({} + {}) {}", base_expr, base_off, pa));
        ("mint_supply_eq", pa.clone(), format!("{}", b45))
    };

    let record = format!(
        "{{ preAuth := {},\n        supply := {},\n        rest := {} }}",
        preauth, supply, rest);
    let post_sup = if m.is_sub { format!("({} - {})", supply, amount) } else { format!("({} + {})", supply, amount) };
    let rw_pre = mint_rw(lemma, &base_arg, &preauth, &pre_args, &supply, &b45, &barrays, preauth_owned);
    let rw_post = mint_rw(lemma, &base_arg, &preauth, &pre_args, &post_sup, &b45, &barrays, preauth_owned);
    // Discharge-route field list (SPL mint: mint_authority@0, supply@36,
    // tail@44) — the `mintSupply_codec` keystone target.
    let field_pre = format!(
        "codecCoarse {} (SVM.Solana.mintFields ({}) {} ({}))",
        base_arg, preauth, supply, rest);
    let field_post = format!(
        "codecCoarse {} (SVM.Solana.mintFields ({}) {} ({}))",
        base_arg, preauth, post_sup, rest);
    Some(AcctBuild { base_arg, record, rw_pre, rw_post, frame, owned, params: Vec::new(), barrays, hyps, agg: None,
        field_pre, field_post })
}

fn mint_rw(lemma: &str, base_arg: &str, preauth: &str, pre_args: &str,
           supply: &str, b45: &str, barrays: &[String], preauth_owned: bool) -> String {
    if preauth_owned {
        // mint_account_eq base b0 p0 p1 p2 p3 supply b45 gA gD gF gAsz gDsz h_b0 h_b45
        let g_a = &barrays[0]; let g_d = &barrays[1]; let g_f = &barrays[2];
        let parts: Vec<&str> = pre_args.split_whitespace().collect(); // [b0, p0, p1, p2, p3, b45]
        format!("{} {} {} {} {} {} {} {} {} {} {} {} {} {} h_{} h_{}",
            lemma, base_arg, parts[0], parts[1], parts[2], parts[3], parts[4],
            supply, b45, g_a, g_d, g_f,
            format!("{}sz", g_a), format!("{}sz", g_d), parts[0], b45)
    } else {
        // mint_supply_eq base supply b45 preAuth gD gF gDsz h_b45
        let g_d = &barrays[1]; let g_f = &barrays[2];
        format!("{} {} {} {} {} {} {} {} h_{}",
            lemma, base_arg, supply, b45, preauth, g_d, g_f,
            format!("{}sz", g_d), b45)
    }
}

#[allow(clippy::too_many_arguments)]
fn render_refinement(
    spec: &RefineSpec, module: &str, builds: &[AcctBuild],
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String], amount: &str,
    n_cu: usize, start_pc: usize, exit_pc: usize,
) -> String {
    let mut nat_params = vars.join(" ");
    for b in builds { for p in &b.params { nat_params.push(' '); nat_params.push_str(p); } }
    let mut barrays: Vec<String> = Vec::new();
    let mut hyps: Vec<String> = Vec::new();
    for b in builds { barrays.extend(b.barrays.iter().cloned()); hyps.extend(b.hyps.iter().cloned()); }

    // AsmRefines arg order: pred cr nCu 0 entry exit rr <addrs> <records> amount setupPre setupPost
    let addr_args: Vec<String> = builds.iter().map(|b| b.base_arg.clone()).collect();
    let record_args: Vec<String> = builds.iter().map(|b| format!("\n      {}", b.record)).collect();

    let mut rw: Vec<String> = Vec::new();
    for b in builds { rw.push(b.rw_pre.clone()); }
    for b in builds { rw.push(b.rw_post.clone()); }

    let frame_atoms: Vec<String> = builds.iter().flat_map(|b| b.frame.iter().cloned()).collect();
    let frame = frame_atoms.join(" **\n      ");

    let uses_mint_codec = builds.iter().any(|b| b.field_pre.contains("mintFields"));
    let mut imports = vec![
        "import SVM.SBPF.Tactic.SL".to_string(),
        "import SVM.Solana.Abstract.Refinement".to_string(),
        "import SVM.Solana.TokenFieldCodec".to_string(),
        format!("import Generated.{}TracedLifted", strip_refinement(module)),
    ];
    if uses_mint_codec { imports.push("import SVM.Solana.MintFieldCodec".to_string()); }
    let uses_transfer_agg = builds.iter().any(|b|
        b.rw_pre.starts_with("src_account_eq") || b.rw_pre.starts_with("dst_account_eq"));
    let uses_mint_agg = builds.iter().any(|b|
        b.rw_pre.starts_with("mint_account_eq") || b.rw_pre.starts_with("mint_supply_eq")
        || b.rw_pre.starts_with("dest_account_eq"));
    if uses_transfer_agg { imports.push("import PToken.TransferAggregation".to_string()); }
    if uses_mint_agg { imports.push("import PToken.MintAggregation".to_string()); }

    // Field-list atoms for the `refines_field` corollary; order matches obligation's account order.
    let field_pre_join = builds.iter().map(|b| b.field_pre.clone())
        .collect::<Vec<_>>().join(" **\n      ");
    let field_post_join = builds.iter().map(|b| b.field_post.clone())
        .collect::<Vec<_>>().join(" **\n      ");
    // Simp set: token keystone always; mint keystone only when a mint account is present (#MintFieldCodec guard).
    let mut reshape_simp = vec![
        "SVM.Solana.tokenAcctBalanceOf_eq", "SVM.Solana.tokenAcctBalanceOf_withAmount",
        "SVM.Solana.tokenAcctBalance_codec",
    ];
    if uses_mint_codec {
        reshape_simp.extend([
            "SVM.Solana.mintSupplyOf_eq", "SVM.Solana.mintSupplyOf_withSupply",
            "SVM.Solana.mintSupply_codec",
        ]);
    }
    let reshape_simp = reshape_simp.join(", ");

    let mut opens = Vec::new();
    if uses_transfer_agg { opens.push("Examples.PTokenTransferAggregation"); }
    if uses_mint_agg { opens.push("Examples.PTokenMintAggregation"); }

    let barray_sig = if barrays.is_empty() { String::new() }
        else { format!("\n    ({} : ByteArray)", barrays.join(" ")) };
    let hyp_sig = if hyps.is_empty() { String::new() }
        else { format!("\n    {}", hyps.join("\n    ")) };

    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
"/-
  {arm} asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen from the lift's atoms + the IDL arm name. Wires the
  trace-guided lift to `{pred}` via the codec-aggregation lemmas +
  `cuTripleWithinMem_frame_right` + `sl_exact`.
-/

{imports}

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory
{opens}

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_params} : Nat){barray_sig}{hyp_sig}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {addrs}{records}
      {amount}
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [{rw}]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

/-- Discharge-route reshape: the `{pred}` obligation is a layout-general
    field-list (`codecCoarse`/`tokenFields`/`mintFields`) obligation. The
    convergence keystones (`tokenAcctBalance_codec` / `mintSupply_codec`)
    rewrite the bespoke `tokenAcctBalanceOf` / `mintSupplyOf` atoms to the
    field-list codec, so qedgen reads the mutated field off the decoded list
    via the library `*_ensures_*` facts (`qedsvm_discharge`). Pairs with
    `refines_asm` (the lift realises the obligation). -/
theorem refines_field
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_params} : Nat){barray_sig}
    (h : SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {addrs}{records}
      {amount}
      ({setup_pre})
      ({setup_post})) :
    cuTripleWithinMem {n} 0 {entry} {exit} cr
      (({setup_pre}) **
      {field_pre})
      (({setup_post}) **
      {field_post})
      rr := by
  unfold SVM.Solana.Abstract.{pred} at h
  simpa only [{reshape_simp}] using h

end Examples.{module}
",
        arm = spec.asm_pred, pred = spec.asm_pred, module = module,
        imports = imports.join("\n"),
        opens = if opens.is_empty() { String::new() } else { format!("open {}", opens.join(" ")) },
        nat_params = nat_params, barray_sig = barray_sig, hyp_sig = hyp_sig,
        n = n_cu, entry = start_pc, exit = exit_pc,
        lift_pre = lift_pre, lift_post = lift_post,
        addrs = addr_args.join(" "), records = record_args.join(""),
        amount = amount,
        setup_pre = setup_pre_s, setup_post = setup_post_s,
        rw = rw.join(",\n      "), frame = frame,
        field_pre = field_pre_join, field_post = field_post_join,
        reshape_simp = reshape_simp,
    )
}

/// Emit a counter-codec refinement: single owned `u64` cell, constant +1 delta.
/// No aggregation (coarse = fine for `u64`), no frame, no `amount` arg.
fn emit_counter_refinement(
    spec: &RefineSpec, lift_module: &str,
    pre: &[Atom], post_clean: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
) -> Option<(String, String, Option<(String, String)>)> {
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // Find the post-state incremented `u64` cell (NatAdd(InitMem, Const) form).
    let mut found: Option<(Expr, i64, Expr, i64)> = None;
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, width, value, .. } = atom {
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
    let addr_arg = if off == 0 { base_l.clone() } else { format!("({} + {})", base_l, off) };
    let counter_pre = fold(&pre_val);
    let record = format!("{{ counter := {} }}", counter_pre);

    // Owned `u64` cell flows through the codec's fine form; everything else stays in setup.
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem { addr_base, addr_off, width, .. } =>
            addr_base.to_lean() == owned_base && *addr_off == off
                && matches!(width, Width::Dword),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_counter_refinement(spec, &module, &addr_arg, &record,
        pre, post_clean, &setup_pre, &setup_post, abs_subst, vars, n_cu, start_pc, exit_pc,
        &counter_pre, delta);
    Some((module, lean, None))
}

/// Render the counter refinement theorem. Proof: `unfold` + `simp [counterValOf]` + `sl_exact`.
fn render_counter_refinement(
    spec: &RefineSpec, module: &str, addr_arg: &str, record: &str,
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    counter_pre: &str, delta: i64,
) -> String {
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
        counter_pre = counter_pre, delta = delta,
        n = n_cu, entry = start_pc, exit = exit_pc,
        lift_pre = lift_pre, lift_post = lift_post,
        addr = addr_arg, record = record,
        setup_pre = setup_pre_s, setup_post = setup_post_s,
    )
}

/// Emit a vault (`AsmRefinesFieldUpdate`) refinement: owns the updated `u64`, frames the rest,
/// reshapes via `codecCoarse_eq_fine`. IDL-driven — new programs cost only a qedspec.
fn emit_vault_refinement(
    spec: &RefineSpec, lift_module: &str,
    pre: &[Atom], post_clean: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    idl: Option<&serde_json::Value>,
    sidecar_layouts: Option<&[AccountLayout]>,
) -> Option<(String, String, Option<(String, String)>)> {
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let layout = resolve_layout(sidecar_layouts, idl, "vault")?;

    let mut updated: Option<(Expr, i64, Expr, i64)> = None; // base, off, pre_val, delta (NatAdd(InitMem, Const))
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, width, value, .. } = atom {
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
                let limbs: Vec<String> = (0..4).map(|_| {
                    let p = format!("o{}", fresh); fresh += 1; params.push(p.clone()); p
                }).collect();
                let rec = format!("⟨{}⟩", limbs.join(", "));
                pre_fields.push(format!("({}, .pubkey {})", off, rec));
                post_fields.push(format!("({}, .pubkey {})", off, rec));
                for (i, limb) in limbs.iter().enumerate() {
                    frame.push(format!("(effectiveAddr {} {} ↦U64 {})", base_l, off + 8 * i as i64, limb));
                }
            }
            FieldKind::U64 => {
                let p = format!("fu{}", fresh); fresh += 1; params.push(p.clone());
                pre_fields.push(format!("({}, .u64 {})", off, p));
                post_fields.push(format!("({}, .u64 {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦U64 {})", base_l, off, p));
            }
            FieldKind::Byte => {
                let p = format!("fb{}", fresh); fresh += 1; params.push(p.clone());
                pre_fields.push(format!("({}, .byte {})", off, p));
                post_fields.push(format!("({}, .byte {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦ₘ {})", base_l, off, p));
            }
            // Blob field: frame as opaque `↦Bytes` gap unless the lift owns bytes inside it (SPLIT path below).
            FieldKind::Bytes(len) => {
                let len = *len as i64;
                // SPLIT if the lift owns bytes inside [off, off+len); else whole field is one opaque gap.
                let owned: Vec<(i64, String)> = (0..len).filter_map(|rel| {
                    cell_val(pre, &base_raw_blob, off + rel, true)
                        .map(|v| (rel, fold(v)))
                }).collect();
                if owned.is_empty() {
                    let g = format!("fg{}", fresh); fresh += 1; ba_params.push(g.clone());
                    pre_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    post_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off, g));
                } else {
                    let mut segs: Vec<String> = Vec::new();
                    let mut cursor = 0i64;
                    for (rel, val) in &owned {
                        if *rel > cursor {
                            // Gap before owned byte: pin size (`fg.size = len`) so segsSL places the byte at `base + rel`.
                            let g = format!("fg{}", fresh); fresh += 1; ba_params.push(g.clone());
                            gap_size_hyps.push((format!("h{}_sz", g), format!("{}.size = {}", g, rel - cursor)));
                            segs.push(format!(".gap {}", g));
                            frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off + cursor, g));
                        }
                        // Owned byte: NOT framed; fine `.byte` atom matches directly. Needs `< 256` hyp.
                        segs.push(format!(".byte ({})", val));
                        owned_blob_offs.push(off + rel);
                        byte_hyps.push(format!("(h_blob{} : {} < 256)", off + rel, val));
                        cursor = rel + 1;
                    }
                    if cursor < len {
                        // Trailing gap (last seg): no size hyp needed — free ByteArray.
                        let g = format!("fg{}", fresh); fresh += 1; ba_params.push(g.clone());
                        segs.push(format!(".gap {}", g));
                        frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off + cursor, g));
                    }
                    let seglist = format!("[{}]", segs.join(", "));
                    pre_fields.push(format!("({}, .blob {})", off, seglist));
                    post_fields.push(format!("({}, .blob {})", off, seglist));
                }
            }
        }
    }
    if !updated_seen { return None; }

    // setup: lift atoms that don't own codec cells (updated u64 + split blob bytes flow through fine form).
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem { addr_base, addr_off, width, .. } =>
            addr_base.to_lean() == owned_base
                && ((*addr_off == upd_off && matches!(width, Width::Dword))
                    || (matches!(width, Width::Byte) && owned_blob_offs.contains(addr_off))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_vault_refinement(spec, &module, &base_l, &pre_fields, &post_fields,
        &frame, &params, &ba_params, pre, post_clean, &setup_pre, &setup_post,
        abs_subst, vars, n_cu, start_pc, exit_pc, upd_off, delta, &upd_pre_l,
        &byte_hyps, &gap_size_hyps);
    Some((module, lean, None))
}

/// Render the vault refinement. Proof: `codecCoarse_eq_fine` reshape → simp fine atoms → `sl_exact`.
fn render_vault_refinement(
    spec: &RefineSpec, module: &str, base_l: &str,
    pre_fields: &[String], post_fields: &[String], frame: &[String], params: &[String],
    ba_params: &[String],
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    upd_off: i64, delta: i64, upd_pre_l: &str, byte_hyps: &[String],
    gap_size_hyps: &[(String, String)],
) -> String {
    let mut nat_params = vars.join(" ");
    for p in params { nat_params.push(' '); nat_params.push_str(p); }
    // `ensures` corollary binders: only params that appear in the field lists (no unused binders).
    let mut ens_nat = upd_pre_l.to_string();
    for p in params { ens_nat.push(' '); ens_nat.push_str(p); }
    let mut ensures_binders = format!("({ens_nat} : Nat)");
    if !ba_params.is_empty() {
        ensures_binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    // ByteArray group only when a blob field is present; keeps non-blob output byte-identical.
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    for h in byte_hyps { binders.push_str(&format!("\n    {}", h)); }
    for (name, prop) in gap_size_hyps { binders.push_str(&format!("\n    ({} : {})", name, prop)); }
    // Simp sets: conditioned on field kinds present to avoid `unusedSimpArgs` and keep non-blob output stable.
    let has_pubkey = pre_fields.iter().any(|f| f.contains(".pubkey"));
    let has_blob = !ba_params.is_empty();
    let mut fine: Vec<String> = vec!["codecFine".into(), "FieldVal.fine".into()];
    if has_pubkey { fine.push("pubkeyIs".into()); }
    if has_blob { fine.push("segsSL".into()); fine.push("FieldSeg.sl".into()); }
    // SPLIT blob: add `FieldSeg.size` + gap-size hyps so running offsets reduce to concrete addresses.
    if !gap_size_hyps.is_empty() {
        fine.push("FieldSeg.size".into());
        for (name, _) in gap_size_hyps { fine.push(name.clone()); }
    }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob { valid.push("segsValid"); valid.push("FieldSeg.valid"); }
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
        upd_off = upd_off, delta = delta,
        valid_tac = valid_tac,
        fine_simp = fine_simp,
        n = n_cu, entry = start_pc, exit = exit_pc,
        lift_pre = lift_pre, lift_post = lift_post,
        base = base_l,
        pre_list = pre_list, post_list = post_list,
        setup_pre = setup_pre_s, setup_post = setup_post_s,
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
    desc:            &RefinementDescriptor,
    lift_module:     &str,
    pre:             &[Atom],
    post_clean:      &[Atom],
    abs_subst:       &std::collections::BTreeMap<String, String>,
    vars:            &[String],
    n_cu:            usize,
    start_pc:        usize,
    exit_pc:         usize,
    // Shape substrate. When the descriptor has no inline layout, its account's layout is
    // resolved from these — the SAME `qed-analysis` path the registry lift uses, so the
    // seam stays name-level (offsets are the IDL's job, not the descriptor's).
    idl:             Option<&serde_json::Value>,
    sidecar_layouts: Option<&[AccountLayout]>,
) -> Option<(String, String, Option<(String, String)>)> {
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

    // Only a `+1` delta is wired (matches the lift's `wrapAdd_one_of_lt` cleaning).
    if desc.op.add_const != 1 {
        eprintln!(
            "descriptor: only op.add_const = 1 is wired (got {}); skipping refinement",
            desc.op.add_const
        );
        return None;
    }

    // Detect the updated `u64` cell in the post (`NatAdd(InitMem, Const)`).
    let mut updated: Option<(Expr, i64, Expr, i64)> = None;
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, width, value, .. } = atom {
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

    // Soundness check: the bytes' delta must match the descriptor's claimed `op`.
    if delta != desc.op.add_const {
        eprintln!(
            "descriptor: op claims +{} but the lift increments the field by {}; \
             refusing to emit a refinement that misdescribes the bytes",
            desc.op.add_const, delta
        );
        return None;
    }

    // Soundness check: the bytes must mutate the field the descriptor names.
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
        Atom::Mem { addr_base, addr_off, width, .. } =>
            addr_base.to_lean() == owned_base && *addr_off == upd_off && matches!(width, Width::Dword),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_descriptor_refinement(
        desc, &module, &base_l, &pre_fields, &post_fields, &frame, &params, &ba_params,
        pre, post_clean, &setup_pre, &setup_post, abs_subst, vars, n_cu, start_pc, exit_pc,
        upd_off, delta, &upd_pre_l,
    );
    Some((module, lean, None))
}

#[allow(clippy::too_many_arguments)]
fn render_descriptor_refinement(
    desc: &RefinementDescriptor, module: &str, base_l: &str,
    pre_fields: &[String], post_fields: &[String], frame: &[String], params: &[String],
    ba_params: &[String],
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    upd_off: i64, delta: i64, upd_pre_l: &str,
) -> String {
    let mut nat_params = vars.join(" ");
    for p in params { nat_params.push(' '); nat_params.push_str(p); }
    // `ensures` corollary binders: only the field-list params (no unused binders).
    let mut ens_nat = upd_pre_l.to_string();
    for p in params { ens_nat.push(' '); ens_nat.push_str(p); }
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
    if has_pubkey { fine.push("pubkeyIs".into()); }
    if has_blob { fine.push("segsSL".into()); fine.push("FieldSeg.sl".into()); }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob { valid.push("segsValid"); valid.push("FieldSeg.valid"); }
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
            frame = frame_s)
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
        upd_off = upd_off, delta = delta,
        valid_tac = valid_tac,
        fine_simp = fine_simp,
        n = n_cu, entry = start_pc, exit = exit_pc,
        lift_pre = lift_pre, lift_post = lift_post,
        base = base_l,
        pre_list = pre_list, post_list = post_list,
        setup_pre = setup_pre_s, setup_post = setup_post_s,
        proof_tail = proof_tail,
    )
}

/// "PTokenMintToRefinement" → "PTokenMintTo".
fn strip_refinement(module: &str) -> String {
    module.strip_suffix("Refinement").unwrap_or(module).to_string()
}
