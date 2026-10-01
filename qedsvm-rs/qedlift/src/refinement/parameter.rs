use qed_analysis::instruction_layout::u64_argument_offset;
use qed_artifacts::{DescriptorOp, RefinementDescriptor};

use super::{RefinementCtx, RefinementOutcome as Outcome, RefinementReason as Reason};
use crate::core::{canon_addr, Atom, Expr, Width};

pub(crate) struct ParameterBinding {
    pub input_base: Expr,
    pub account_offset: i64,
    pub argument_offset: i64,
}

pub(crate) fn resolve_parameter(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
) -> Result<ParameterBinding, Outcome> {
    let missing = |message| Outcome::unsupported(Reason::MissingParameterBinding, message);
    let invalid = |message| Outcome::rejected(Reason::InvalidParameterBinding, message);
    let DescriptorOp::AddParam { add_param } = &desc.op else {
        return Err(missing("operation has no parameter"));
    };
    if desc.schema_version != 3 {
        return Err(missing("parameter binding requires descriptor schema v3"));
    }
    let input = desc
        .input_layout
        .as_ref()
        .ok_or_else(|| missing("parameter binding requires input_layout"))?;
    if input.account_index >= input.account_data_lengths.len() {
        return Err(invalid("account_index is outside input_layout".to_string()));
    }
    let offsets = qed_analysis::input_layout::aligned_input_offsets(&input.account_data_lengths)
        .map_err(|message| invalid(message.into()))?;
    let account_offset = offsets.account_data[input.account_index];
    let idl = ctx
        .idl
        .ok_or_else(|| missing("parameter binding requires an IDL"))?;
    let handler = desc
        .handler
        .as_deref()
        .ok_or_else(|| missing("parameter binding requires a handler"))?;
    let relative = u64_argument_offset(idl, handler, add_param)
        .map_err(|message| Outcome::rejected(Reason::InvalidParameterBinding, message))?;
    let argument_offset = offsets
        .instruction_data
        .checked_add(relative)
        .and_then(|n| i64::try_from(n).ok())
        .ok_or_else(|| invalid("argument offset overflow".into()))?;
    // Only entry-point lifts establish r1 as the serialized input pointer.
    if ctx.start_pc != 0 {
        return Err(missing(
            "parameter binding requires a lift from the program entry point",
        ));
    }
    let input_base = ctx
        .pre
        .iter()
        .find_map(|a| match a {
            Atom::Reg(1, value @ Expr::InitReg(_)) => Some(value.clone()),
            _ => None,
        })
        .ok_or_else(|| missing("entry r1 input pointer is unavailable"))?;
    Ok(ParameterBinding {
        input_base,
        account_offset: i64::try_from(account_offset)
            .map_err(|_| invalid("account offset overflow".into()))?,
        argument_offset,
    })
}

impl ParameterBinding {
    pub(crate) fn matches_value(&self, value: &str, ctx: RefinementCtx<'_>) -> bool {
        ctx.pre.iter().any(|atom| matches!(atom,
            Atom::Mem { addr_base, addr_off, width: Width::Dword, value: v, .. }
            if crate::emit::fold_abstractions(v.to_lean(), ctx.abs_subst) == value
                && canon_addr(addr_base, *addr_off) == canon_addr(&self.input_base, self.argument_offset)))
    }
}
