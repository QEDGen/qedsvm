use super::core::Expr;

/// Conditional jump kind for a happy-path branch hypothesis; `sl_block_auto` doesn't collapse these, so they surface in the theorem signature.
#[derive(Clone, Debug)]
pub(super) enum BranchKind {
    JeqImm,
    JneImm,
    JgtImm,
    JsgtImm,
    JsleImm,
    JltImm,
    JleImm,
    JsltImm,
    JgeImm,
    JsgeImm,
    JsetImm,
    JeqReg,
    JneReg,
    JltReg,
    JsleReg,
    JgtReg,
    JleReg,
    JsgeReg,
    JgeReg,
    JsgtReg,
    JsltReg,
    JsetReg,
}

#[derive(Clone, Debug)]
pub(super) struct BranchHyp {
    pub(super) kind: BranchKind,
    pub(super) dst_value: Expr,
    /// Src register's symbolic value for reg-form jumps; `None` for imm-form.
    pub(super) src_value: Option<Expr>,
    pub(super) imm: i64,
    /// `true` if branch taken; `false` for fall-through. Determines hypothesis form:
    /// jeq-taken -> `vDst = toU64 imm`, jeq-not-taken -> `vDst != toU64 imm`; jne symmetric.
    pub(super) taken: bool,
}

impl BranchHyp {
    pub(super) fn lean_hyp(&self) -> String {
        let v = self.dst_value.to_lean();
        let s = self
            .src_value
            .as_ref()
            .map(|e| e.to_lean())
            .unwrap_or_default();
        // atom_lean() parenthesises compound exprs for use under `toSigned64` (prefix application
        // that grabs only the head: `toSigned64 wrapAdd a b` misparses as `(toSigned64 wrapAdd) a b`).
        let va = self.dst_value.atom_lean();
        let sa = self
            .src_value
            .as_ref()
            .map(|e| e.atom_lean())
            .unwrap_or_default();
        // Parenthesise negative imm: `toU64 -5` parses as `(toU64) - 5` (Int->Nat type error).
        let im = if self.imm < 0 {
            format!("({})", self.imm)
        } else {
            format!("{}", self.imm)
        };
        match (self.kind.clone(), self.taken) {
            (BranchKind::JeqImm, false) => format!("{} ≠ toU64 {}", v, im),
            (BranchKind::JeqImm, true) => format!("{} = toU64 {}", v, im),
            (BranchKind::JneImm, false) => format!("{} = toU64 {}", v, im),
            (BranchKind::JneImm, true) => format!("{} ≠ toU64 {}", v, im),
            // `jgt` unsigned >; taken/not-taken accepted by Lean helpers via if_pos/if_neg.
            (BranchKind::JgtImm, false) => format!("¬ {} > toU64 {}", v, im),
            (BranchKind::JgtImm, true) => format!("{} > toU64 {}", v, im),
            // `jsgt` signed >: compares `toSigned64 vDst > toSigned64 (toU64 imm)`.
            (BranchKind::JsgtImm, false) => {
                format!("¬ toSigned64 {} > toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JsgtImm, true) => {
                format!("toSigned64 {} > toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JsleImm, false) => {
                format!("¬ toSigned64 {} ≤ toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JsleImm, true) => {
                format!("toSigned64 {} ≤ toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JltImm, false) => format!("¬ {} < toU64 {}", v, im),
            (BranchKind::JltImm, true) => format!("{} < toU64 {}", v, im),
            (BranchKind::JleImm, false) => format!("¬ {} ≤ toU64 {}", v, im),
            (BranchKind::JleImm, true) => format!("{} ≤ toU64 {}", v, im),
            (BranchKind::JsltImm, false) => {
                format!("¬ toSigned64 {} < toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JsltImm, true) => {
                format!("toSigned64 {} < toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JgeImm, false) => format!("¬ {} ≥ toU64 {}", v, im),
            (BranchKind::JgeImm, true) => format!("{} ≥ toU64 {}", v, im),
            (BranchKind::JsgeImm, false) => {
                format!("¬ toSigned64 {} ≥ toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JsgeImm, true) => {
                format!("toSigned64 {} ≥ toSigned64 (toU64 {})", va, im)
            }
            (BranchKind::JsetImm, false) => format!("¬ {} &&& toU64 {} ≠ 0", v, im),
            (BranchKind::JsetImm, true) => format!("{} &&& toU64 {} ≠ 0", v, im),
            (BranchKind::JeqReg, false) => format!("{} ≠ {}", v, s),
            (BranchKind::JeqReg, true) => format!("{} = {}", v, s),
            (BranchKind::JneReg, false) => format!("{} = {}", v, s),
            (BranchKind::JneReg, true) => format!("{} ≠ {}", v, s),
            (BranchKind::JltReg, false) => format!("¬ {} < {}", v, s),
            (BranchKind::JltReg, true) => format!("{} < {}", v, s),
            (BranchKind::JgtReg, false) => format!("¬ {} > {}", v, s),
            (BranchKind::JgtReg, true) => format!("{} > {}", v, s),
            (BranchKind::JleReg, false) => format!("¬ {} ≤ {}", v, s),
            (BranchKind::JleReg, true) => format!("{} ≤ {}", v, s),
            (BranchKind::JsgeReg, false) => format!("¬ toSigned64 {} ≥ toSigned64 {}", va, sa),
            (BranchKind::JsgeReg, true) => format!("toSigned64 {} ≥ toSigned64 {}", va, sa),
            (BranchKind::JgeReg, false) => format!("¬ {} ≥ {}", v, s),
            (BranchKind::JgeReg, true) => format!("{} ≥ {}", v, s),
            (BranchKind::JsgtReg, false) => format!("¬ toSigned64 {} > toSigned64 {}", va, sa),
            (BranchKind::JsgtReg, true) => format!("toSigned64 {} > toSigned64 {}", va, sa),
            (BranchKind::JsltReg, false) => format!("¬ toSigned64 {} < toSigned64 {}", va, sa),
            (BranchKind::JsltReg, true) => format!("toSigned64 {} < toSigned64 {}", va, sa),
            (BranchKind::JsetReg, false) => format!("¬ {} &&& {} ≠ 0", v, s),
            (BranchKind::JsetReg, true) => format!("{} &&& {} ≠ 0", v, s),
            (BranchKind::JsleReg, false) => format!("¬ toSigned64 {} ≤ toSigned64 {}", va, sa),
            (BranchKind::JsleReg, true) => format!("toSigned64 {} ≤ toSigned64 {}", va, sa),
        }
    }

    pub(super) fn name(&self, idx: usize) -> String {
        format!("h_branch{}", idx)
    }
}
