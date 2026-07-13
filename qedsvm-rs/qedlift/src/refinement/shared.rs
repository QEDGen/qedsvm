use super::super::core::{Atom, Expr, Width};

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

/// "PTokenMintToRefinement" → "PTokenMintTo".
pub(super) fn strip_refinement(module: &str) -> String {
    module
        .strip_suffix("Refinement")
        .unwrap_or(module)
        .to_string()
}
