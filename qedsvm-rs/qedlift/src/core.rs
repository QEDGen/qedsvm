/// Symbolic Nat expression during execution; stringified to Lean source via `to_lean`.
#[derive(Clone, Debug)]
pub(super) enum Expr {
    InitReg(String),
    InitMem(String),
    Const(i64),
    ToU64(Box<Expr>),
    Mod(Box<Expr>, u64),
    WrapAdd(Box<Expr>, Box<Expr>),
    WrapSub(Box<Expr>, Box<Expr>),
    WrapMul(Box<Expr>, Box<Expr>),
    /// Plain `Nat.add a b` — `call_local_spec`'s `r10 + 0x1000` uses Nat add, not `wrapAdd`.
    NatAdd(Box<Expr>, Box<Expr>),
    /// `(a &&& toU64 imm) % U64_MODULUS` — output of `and64_imm_spec`; `toU64 imm` rendered inside `to_lean`.
    AndU64Imm(Box<Expr>, i64),
    /// `(a <<< (toU64 imm % 64)) % U64_MODULUS` — output of `lsh64_imm_spec`.
    LshU64Imm(Box<Expr>, i64),
    /// `toU64 imm % 2 ^ (2 * 8)` — matches `sth_spec`'s post.
    StHalfImm(i64),
    /// `toU64 imm % 2 ^ (4 * 8)` — matches `stw_spec`'s post (`writeByWidth` truncates to 32 bits).
    StWordImm(i64),
    /// `toU64 imm % 2 ^ (8 * 8)` — matches `stdw_spec`'s post.
    StDwordImm(i64),
    /// `a >>> (toU64 imm % 64)` — output of `rsh64_imm_spec`; no `% U64_MODULUS` (right shift never grows).
    RshU64Imm(Box<Expr>, i64),
    /// Render-only `a - b` (Nat sub): exposes a `wrapSub` debit cleanly in the balance corollary (justified by `wrapSub_of_le`).
    CleanSub(Box<Expr>, Box<Expr>),
    /// LE Horner combination of 8 byte cells from `ldxdw` over a hot (byte-demoted) region; matches `ldxdw_bytes_spec`'s post.
    ByteCombo(Vec<Expr>),
    /// Pre-rendered Lean term for ALU results without a bespoke variant (or/xor/div/mod/neg, reg shifts, 32-bit ops). Opaque to the balance corollary; always parenthesised as a function argument.
    Raw(String),
    /// A `Raw` render whose value is CLOSED (no free variables) and known —
    /// e.g. a constant rodata table address built through `|||`/`arsh` chains
    /// the structured variants don't cover. Renders byte-identically to
    /// `Raw` (zero regen churn, `sl_block_auto` shape preserved); the carried
    /// value lets the H8 witness evaluate the address root.
    RawConst(String, u64),
}

impl Expr {
    pub(super) fn to_lean(&self) -> String {
        match self {
            Expr::Raw(s) => s.clone(),
            Expr::RawConst(s, _) => s.clone(),
            Expr::InitReg(n) | Expr::InitMem(n) => n.clone(),
            Expr::Const(n) => format!("{}", n),
            Expr::ToU64(e) => format!("toU64 {}", e.atom_lean()),
            Expr::Mod(e, m) => format!("{} % {}", e.atom_lean(), m),
            Expr::WrapAdd(a, b) => format!("wrapAdd {} {}", a.atom_lean(), b.atom_lean()),
            Expr::WrapSub(a, b) => format!("wrapSub {} {}", a.atom_lean(), b.atom_lean()),
            Expr::WrapMul(a, b) => format!("wrapMul {} {}", a.atom_lean(), b.atom_lean()),
            Expr::NatAdd(a, b) => format!("{} + {}", a.atom_lean(), b.atom_lean()),
            Expr::AndU64Imm(a, imm) => {
                let imm_lean = if *imm < 0 {
                    format!("({})", imm)
                } else {
                    format!("{}", imm)
                };
                format!("({} &&& toU64 {}) % U64_MODULUS", a.atom_lean(), imm_lean)
            }
            Expr::LshU64Imm(a, imm) => {
                let imm_lean = if *imm < 0 {
                    format!("({})", imm)
                } else {
                    format!("{}", imm)
                };
                format!(
                    "({} <<< (toU64 {} % 64)) % U64_MODULUS",
                    a.atom_lean(),
                    imm_lean
                )
            }
            Expr::StHalfImm(imm) => {
                let imm_lean = if *imm < 0 {
                    format!("({})", imm)
                } else {
                    format!("{}", imm)
                };
                format!("toU64 {} % 2 ^ (2 * 8)", imm_lean)
            }
            Expr::StWordImm(imm) => {
                let imm_lean = if *imm < 0 {
                    format!("({})", imm)
                } else {
                    format!("{}", imm)
                };
                format!("toU64 {} % 2 ^ (4 * 8)", imm_lean)
            }
            Expr::StDwordImm(imm) => {
                let imm_lean = if *imm < 0 {
                    format!("({})", imm)
                } else {
                    format!("{}", imm)
                };
                format!("toU64 {} % 2 ^ (8 * 8)", imm_lean)
            }
            Expr::RshU64Imm(a, imm) => {
                let imm_lean = if *imm < 0 {
                    format!("({})", imm)
                } else {
                    format!("{}", imm)
                };
                format!("{} >>> (toU64 {} % 64)", a.atom_lean(), imm_lean)
            }
            Expr::CleanSub(a, b) => format!("{} - {}", a.atom_lean(), b.atom_lean()),
            Expr::ByteCombo(bs) => {
                // Horner fold: innermost pair unparenthesised, matching `ldxdw_bytes_spec`'s post.
                let mut it = bs.iter().rev();
                let mut s = it.next().map(|e| e.atom_lean()).unwrap_or_default();
                let mut first = true;
                for b in it {
                    if first {
                        s = format!("{} + 256 * {}", b.atom_lean(), s);
                        first = false;
                    } else {
                        s = format!("{} + 256 * ({})", b.atom_lean(), s);
                    }
                }
                s
            }
        }
    }

    /// Lean rendering as a function argument (parenthesised when not already atomic).
    pub(super) fn atom_lean(&self) -> String {
        match self {
            Expr::Raw(s) => format!("({})", s),
            Expr::RawConst(s, _) => format!("({})", s),
            Expr::InitReg(_) | Expr::InitMem(_) => self.to_lean(),
            // Negative constants need parens: `toU64 -1` parses as subtraction otherwise.
            Expr::Const(n) if *n < 0 => format!("({})", n),
            Expr::Const(_) => self.to_lean(),
            _ => format!("({})", self.to_lean()),
        }
    }
}

/// Load/store width — determines Lean memory notation (↦ₘ byte, ↦U16/32/64 wider).
#[derive(Clone, Copy, Debug)]
pub(super) enum Width {
    Byte,
    Halfword,
    Word,
    Dword,
}

impl Width {
    pub(super) fn lean_arrow(&self) -> &'static str {
        match self {
            Width::Byte => "↦ₘ",
            Width::Halfword => "↦U16",
            Width::Word => "↦U32",
            Width::Dword => "↦U64",
        }
    }
}

/// Render a memory offset for `effectiveAddr base off`. Negative offsets MUST be parenthesised: `effectiveAddr b -8` parses as `(effectiveAddr b) - 8` (HSub type error, partial application).
pub(super) fn lean_off(off: i64) -> String {
    if off < 0 {
        format!("({})", off)
    } else {
        format!("{}", off)
    }
}

/// Render `arsh{32,64}`'s post as a parenthesised Lean term matching `arsh{32,64}_{imm,reg}_spec` (used as `Expr::Raw`). Parens required: `↦ᵣ` can't take a bare `let`.
pub(super) fn arsh_render(vold: &str, shift_src: &str, bits: u32) -> String {
    let m = if bits == 64 {
        "U64_MODULUS"
    } else {
        "U32_MODULUS"
    };
    if bits == 64 {
        format!(
            "(let shift := {s} % 64; if {v} < {m} / 2 then {v} >>> shift \
                 else (let shifted := {v} >>> shift; \
                 let highBits := ({m} - 1) - ({m} / (2 ^ shift) - 1); \
                 (shifted ||| highBits) % {m}))",
            s = shift_src,
            v = vold,
            m = m
        )
    } else {
        format!(
            "(let shift := {s} % 32; let a := {v} % {m}; \
                 if a < {m} / 2 then a >>> shift \
                 else (let shifted := a >>> shift; \
                 let highBits := ({m} - 1) - ({m} / (2 ^ shift) - 1); \
                 (shifted ||| highBits) % {m}))",
            s = shift_src,
            v = vold,
            m = m
        )
    }
}

/// Variable-length byte blob (`↦Bytes`). Pre-state is a fresh symbolic `ByteArray`; a memset rewrites it to a `Replicate` payload.
#[derive(Clone, Debug)]
pub(super) enum BytesVal {
    /// Fresh symbolic byte-array name; `.size = <r3>` bound surfaced as a hypothesis via `memset_blobs`, not stored here.
    Sym(String),
    /// `replicateByte (fill % 256).toUInt8 count` — post-state of `sol_memset_(dst, fill, count)`.
    Replicate { fill: Expr, count: Expr },
}

impl BytesVal {
    pub(super) fn to_lean(&self) -> String {
        match self {
            BytesVal::Sym(name) => name.clone(),
            BytesVal::Replicate { fill, count } => format!(
                "replicateByte ({} % 256).toUInt8 {}",
                fill.atom_lean(),
                count.atom_lean(),
            ),
        }
    }
}

/// One precondition atom: register binding, fixed-width memory cell, or `↦Bytes` blob (from `sol_memset_` etc.).
#[derive(Clone, Debug)]
pub(super) enum Atom {
    Reg(u8, Expr),
    Mem {
        addr_base: Expr,
        addr_off: i64,
        width: Width,
        value: Expr,
        delta: i64,
    },
    /// `addr ↦Bytes <bytes>`. Address is the raw syscall `r1` value (no `effectiveAddr` — `memBytesIs` takes a bare Nat), matching `call_sol_memset_spec`.
    Bytes {
        addr: Expr,
        value: BytesVal,
    },
    /// `↦Bytes32` referencing a named Lean `ByteArray` constant (e.g. `SysvarData.rentId` for `sol_get_sysvar`'s id read). Read-only: identical pre and post.
    Bytes32 {
        addr: Expr,
        name: String,
    },
    /// `↦ReturnData <bytes>`. The global `State.returnData` buffer (not memory-addressed). Pre is a fresh symbolic `ByteArray` (`sol_set_return_data`'s old value); the post flips it to the input blob via `state.returndata_post()`.
    ReturnData {
        value: BytesVal,
    },
}

pub(super) fn reg_lit(n: u8) -> &'static str {
    match n {
        0 => "r0",
        1 => "r1",
        2 => "r2",
        3 => "r3",
        4 => "r4",
        5 => "r5",
        6 => "r6",
        7 => "r7",
        8 => "r8",
        9 => "r9",
        10 => "r10",
        _ => "r0",
    }
}

pub(super) fn reg_initial_name(n: u8) -> String {
    match n {
        1 => "baseAddr".to_string(), // r1 = input ptr by Solana ABI
        _ => format!("vR{}Old", n),
    }
}

/// One memory cell in the symbolic walk. Address is the SYMBOLIC value of `base_reg` at access time — `[r1+0]` at two different PCs is two distinct cells if `r1` changed.
#[derive(Clone, Debug)]
pub(super) struct MemCell {
    pub(super) addr_base: Expr,
    pub(super) addr_off: i64,
    pub(super) width: Width,
    pub(super) value: Expr,
    /// Byte offset within a hot (byte-demoted) region relative to `(addr_base, addr_off)`. 0 for ordinary cells. Renders as `effectiveAddr base off + delta`, matching `ldxdw_bytes_spec`'s atom shape (H8 Phase B).
    pub(super) delta: i64,
}

impl MemCell {
    /// Stable key over (rendered address, width) — same rendering = same physical cell.
    pub(super) fn key(&self) -> (String, i64, i64, u8) {
        (
            self.addr_base.to_lean(),
            self.addr_off,
            self.delta,
            self.width as u8,
        )
    }
}

/// Fold a constant out of an `Expr` (through `toU64`).
pub(super) fn const_of_expr(e: &Expr) -> Option<i64> {
    match e {
        Expr::Const(k) => Some(*k),
        Expr::ToU64(inner) => const_of_expr(inner),
        _ => None,
    }
}

/// Fold constant `wrapAdd`/`wrapSub`/`NatAdd` layers of an address into a canonical `(root, displacement) pair.
pub(super) fn canon_addr(base: &Expr, off: i64) -> (String, i64) {
    fn go(e: &Expr, acc: i64) -> Option<(String, i64)> {
        match e {
            Expr::InitReg(_) | Expr::InitMem(_) => Some((e.to_lean(), acc)),
            Expr::Const(k) => Some(("«absolute»".to_string(), acc.wrapping_add(*k))),
            Expr::ToU64(inner) => go(inner, acc),
            Expr::WrapAdd(a, b) | Expr::NatAdd(a, b) => {
                if let Some(k) = const_of_expr(b) {
                    go(a, acc.wrapping_add(k))
                } else if let Some(k) = const_of_expr(a) {
                    go(b, acc.wrapping_add(k))
                } else {
                    None
                }
            }
            Expr::WrapSub(a, b) => {
                if let Some(k) = const_of_expr(b) {
                    go(a, acc.wrapping_sub(k))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    go(base, off).unwrap_or_else(|| (base.to_lean(), off))
}

/// Like `canon_addr` but returns the root sub-`Expr` instead of its rendering — the satisfiability-witness builder needs the tree to solve/evaluate.
pub(super) fn canon_root_expr(e: &Expr, acc: i64) -> (Option<&Expr>, i64) {
    match e {
        Expr::InitReg(_) | Expr::InitMem(_) => (Some(e), acc),
        Expr::Const(k) => (None, acc.wrapping_add(*k)),
        Expr::ToU64(inner) => canon_root_expr(inner, acc),
        Expr::WrapAdd(a, b) | Expr::NatAdd(a, b) => {
            if let Some(k) = const_of_expr(b) {
                canon_root_expr(a, acc.wrapping_add(k))
            } else if let Some(k) = const_of_expr(a) {
                canon_root_expr(b, acc.wrapping_add(k))
            } else {
                (Some(e), acc)
            }
        }
        Expr::WrapSub(a, b) => {
            if let Some(k) = const_of_expr(b) {
                canon_root_expr(a, acc.wrapping_sub(k))
            } else {
                (Some(e), acc)
            }
        }
        _ => (Some(e), acc),
    }
}

/// Evaluate an `Expr` to `u64` under a variable assignment, mirroring Lean semantics. `None` for unassigned variables or `Raw`.
pub(super) fn eval_expr(e: &Expr, env: &std::collections::BTreeMap<String, u64>) -> Option<u64> {
    match e {
        Expr::InitReg(n) | Expr::InitMem(n) => env.get(n).copied(),
        Expr::Const(k) => {
            if *k >= 0 {
                Some(*k as u64)
            } else {
                None
            }
        }
        Expr::ToU64(inner) => match inner.as_ref() {
            Expr::Const(k) => Some(*k as u64),
            other => eval_expr(other, env),
        },
        Expr::Mod(a, m) => eval_expr(a, env).map(|v| if *m == 0 { v } else { v % *m }),
        Expr::WrapAdd(a, b) => Some(eval_expr(a, env)?.wrapping_add(eval_expr(b, env)?)),
        Expr::WrapSub(a, b) => Some(eval_expr(a, env)?.wrapping_sub(eval_expr(b, env)?)),
        Expr::WrapMul(a, b) => Some(eval_expr(a, env)?.wrapping_mul(eval_expr(b, env)?)),
        // Nat add: overflow would diverge from Lean's Nat (where addition is unbounded), so fail closed.
        Expr::NatAdd(a, b) => eval_expr(a, env)?.checked_add(eval_expr(b, env)?),
        Expr::AndU64Imm(a, imm) => Some(eval_expr(a, env)? & (*imm as u64)),
        Expr::LshU64Imm(a, imm) => Some(eval_expr(a, env)?.wrapping_shl((*imm as u64 % 64) as u32)),
        Expr::RshU64Imm(a, imm) => Some(eval_expr(a, env)? >> (*imm as u64 % 64)),
        Expr::StHalfImm(imm) => Some((*imm as u64) % (1 << 16)),
        Expr::StWordImm(imm) => Some((*imm as u64) % (1 << 32)),
        Expr::StDwordImm(imm) => Some(*imm as u64),
        Expr::CleanSub(a, b) => eval_expr(a, env)?.checked_sub(eval_expr(b, env)?),
        Expr::ByteCombo(bs) => {
            let mut acc: u64 = 0;
            for b in bs.iter().rev() {
                acc = acc.wrapping_mul(256).wrapping_add(eval_expr(b, env)?);
            }
            Some(acc)
        }
        Expr::Raw(_) => None,
        Expr::RawConst(_, v) => Some(*v),
    }
}

/// Assign the single unassigned variable in an invertible address expression so it evaluates to `target`.
pub(super) fn solve_expr(
    e: &Expr,
    target: u64,
    env: &mut std::collections::BTreeMap<String, u64>,
) -> bool {
    // Fully evaluable under current env: can only check, not steer.
    if let Some(v) = eval_expr(e, env) {
        return v == target;
    }
    match e {
        Expr::InitReg(n) | Expr::InitMem(n) => {
            env.insert(n.clone(), target);
            true
        }
        Expr::ToU64(inner) => solve_expr(inner, target, env),
        Expr::Mod(a, m) => {
            if *m != 0 && target >= *m {
                return false;
            }
            solve_expr(a, target, env)
        }
        Expr::WrapAdd(a, b) => {
            if let Some(va) = eval_expr(a, env) {
                solve_expr(b, target.wrapping_sub(va), env)
            } else if let Some(vb) = eval_expr(b, env) {
                solve_expr(a, target.wrapping_sub(vb), env)
            } else {
                false
            }
        }
        Expr::WrapSub(a, b) => {
            if let Some(vb) = eval_expr(b, env) {
                solve_expr(a, target.wrapping_add(vb), env)
            } else if let Some(va) = eval_expr(a, env) {
                solve_expr(b, va.wrapping_sub(target), env)
            } else {
                false
            }
        }
        Expr::NatAdd(a, b) => {
            if let Some(va) = eval_expr(a, env) {
                target
                    .checked_sub(va)
                    .is_some_and(|t| solve_expr(b, t, env))
            } else if let Some(vb) = eval_expr(b, env) {
                target
                    .checked_sub(vb)
                    .is_some_and(|t| solve_expr(a, t, env))
            } else {
                false
            }
        }
        Expr::AndU64Imm(a, imm) => {
            // target must be a fixed point of the mask; then target itself is a valid pre-image.
            if target & (*imm as u64) != target {
                return false;
            }
            solve_expr(a, target, env)
        }
        Expr::ByteCombo(bs) => {
            // LE: element i carries byte i of target (elements past 8 must be 0). Re-evaluate to confirm (a conflicting constant fails).
            for (i, b) in bs.iter().enumerate() {
                let byte = if i < 8 { (target >> (8 * i)) & 0xff } else { 0 };
                if !solve_expr(b, byte, env) {
                    return false;
                }
            }
            eval_expr(e, env) == Some(target)
        }
        _ => false,
    }
}

pub(super) fn w_short(w: Width) -> &'static str {
    match w {
        Width::Byte => "B",
        Width::Halfword => "H",
        Width::Word => "W",
        Width::Dword => "D",
    }
}
