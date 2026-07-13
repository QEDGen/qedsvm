mod counter;
mod descriptor;
mod shared;
mod token;
mod vault;

use qed_analysis::layout::AccountLayout;

use super::core::{Atom, Expr};
use super::input::RefinementDescriptor;

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

pub(super) fn cell_val<'a>(
    atoms: &'a [Atom],
    base_raw: &str,
    off: i64,
    byte: bool,
) -> Option<&'a Expr> {
    shared::cell_val(atoms, base_raw, off, byte)
}

pub(super) fn cell_val_dword<'a>(atoms: &'a [Atom], base_raw: &str, off: i64) -> Option<&'a Expr> {
    shared::cell_val_dword(atoms, base_raw, off)
}

pub(super) fn emit_descriptor_refinement(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
) -> Option<(String, String)> {
    descriptor::emit_descriptor_refinement(desc, ctx)
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

pub(super) fn emit_refinement(arm_name: &str, ctx: RefinementCtx<'_>) -> Option<(String, String)> {
    let spec = refine_registry(arm_name)?;

    if spec
        .accounts
        .iter()
        .all(|(_, codec)| matches!(codec, CodecKind::Counter))
    {
        return counter::emit_counter_refinement(&spec, ctx);
    }

    if spec
        .accounts
        .iter()
        .all(|(_, codec)| matches!(codec, CodecKind::Vault))
    {
        return vault::emit_vault_refinement(&spec, ctx);
    }

    token::emit_token_refinement(&spec, ctx)
}
