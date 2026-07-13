use super::branch::BranchHyp;
use super::core::{canon_addr, reg_initial_name, w_short, Atom, BytesVal, Expr, MemCell, Width};
use super::diagnostic::{DiagnosticKind, LiftError};

#[derive(Default)]
struct FreshNames {
    next: std::cell::Cell<u32>,
    reserved: std::cell::RefCell<std::collections::VecDeque<u32>>,
}

impl FreshNames {
    fn reserve(&self) -> u32 {
        let index = self.next.get();
        self.next.set(index + 1);
        self.reserved.borrow_mut().push_back(index);
        index
    }

    fn allocate(&self) -> u32 {
        self.reserved.borrow_mut().pop_front().unwrap_or_else(|| {
            let index = self.next.get();
            self.next.set(index + 1);
            index
        })
    }

    fn finish_prepared_step(&self) -> Result<(), LiftError> {
        if self.reserved.borrow().is_empty() {
            Ok(())
        } else {
            Err(LiftError::new(
                DiagnosticKind::Other,
                "qedlift: prepared symbolic names were not consumed by instruction execution",
            ))
        }
    }
}

// Symbolic executor: walks decoded eBPF insns, synthesizes pre/post for `cuTripleWithinMem n 0 0 n cr PRE POST RR`, discharged by `sl_block_auto`.

/// One region-requirement clause collected during the symbolic walk:
/// `(base, offset, width, writable, variable-length override)`.
pub(super) type RegionRequirement = (Expr, i64, Width, bool, Option<(Expr, Expr)>);

#[derive(Default)]
pub(super) struct SymState {
    /// Symbolic register values; absent entries are treated as `InitReg(reg_initial_name(r))`.
    pub(super) regs: std::collections::BTreeMap<u8, Expr>,
    /// Pre-condition atoms collected in *first-touched* order.
    pub(super) pre: Vec<Atom>,
    /// Memory cells the slice touched; `base` is the SYMBOLIC register value at access time (so `[r1+0]` after `add64 r1,8` is a distinct cell). Linear search; small N.
    pub(super) mem: Vec<MemCell>,
    /// Single allocator for memory, syscall, and prepared-step identifiers.
    names: FreshNames,
    /// `(var, k)` pairs for memory loads with a `< 2^k` side condition (k=16/32/64 for ldxh/ldxw/ldxdw). Emitted as `h<var>_lt` hypotheses in the theorem signature.
    pub(super) u64_load_vars: Vec<(String, u32)>,
    /// Conditional jumps on the happy-path walk; each adds a path hypothesis to the theorem signature.
    pub(super) branch_hyps: Vec<BranchHyp>,
    /// `(resume_pc, [r6..r10] at call time)` pushed by `call_local`, popped by `exit`. Full r6..r10 saved because a callee may clobber r6..r9 — `exit_pops` needs the frame from call time, not exit time.
    pub(super) call_stack: Vec<(usize, [Expr; 5])>,
    /// Set on first `call_local`; emission then adds `r6..r10` and `callStackIs []` to the pre-condition.
    pub(super) saw_call: bool,
    /// rr clauses in walk order (load → `containsRange`, store → `containsWritable`), matching `slBlockIter`'s left-fold. `memset_override = Some((dst, count))` is a variable-length `containsWritable` clause (H6: `MemOps.execSet.guardWrite`); fixed fields ignored, address rendered raw without `effectiveAddr`.
    pub(super) rr_walk: Vec<RegionRequirement>,
    /// Post-state of `↦Bytes` blobs written by `sol_memset_`, keyed by rendered address. Read by `post_atoms` to transform pre `Sym` → post `Replicate`.
    pub(super) byte_blob_post: std::collections::BTreeMap<String, BytesVal>,
    /// PC → Lean `Syscall` constructor for identified host syscalls; CodeReq renders as `.call <ctor>` instead of `.call_local`.
    pub(super) syscall_pcs: std::collections::BTreeMap<usize, &'static str>,
    /// `(nCu_var, hCu_hyp, syscall_ctor)` per syscall with surfaced CU cost. `syscallCu` is data-dependent (∝ r3 for mem ops), so the upper bound is an assumption the lift can't discharge.
    pub(super) syscall_cu_vars: Vec<(String, String, &'static str)>,
    /// `(bytes_sym, size_rendered)` per memset blob; emitted as a `ByteArray` param + `.size = <count>` hypothesis (spec's `hbs` obligation).
    pub(super) memset_blobs: Vec<(String, String)>,
    /// Bare `ByteArray` params (no size hypothesis), e.g. `sol_set_return_data`'s old returnData buffer — arbitrary, so unconstrained.
    pub(super) bytearray_vars: Vec<String>,
    /// Post-state value of the `↦ReturnData` atom (`sol_set_return_data` copies the input blob into returnData). `None` = no returnData atom in the pre.
    pub(super) returndata_post: Option<BytesVal>,
    /// `(hyp_name, prop)` side-condition hypotheses emitted verbatim (e.g. divisor `v ≠ 0` for `div/mod` reg-form — symbolic divisor, so caller's obligation).
    pub(super) side_hyps: Vec<(String, String)>,
    /// Canonical `(root, lo, hi_exclusive, key_render)` footprint of every materialized atom. Consulted on each new materialization to detect overlaps — an overlapping sepConj is unsatisfiable (vacuous theorem, soundness audit H8).
    pub(super) atom_spans: Vec<(String, i64, i64, String)>,
    /// Footprint-overlap errors from `note_access`; reported as a hard error after the walk (fail-closed: never emit a vacuous theorem; full inventory aids Phase B planning).
    pub(super) overlap_errors: Vec<String>,
    /// `(lhs, rhs)` set when an access resolved to an existing cell under a DIFFERENT rendering (Phase A aliasing). Walk loop drains it into `h_alias_<pc> : lhs = rhs` (discharged by `decide`); the spec-call `rw`s it so the chain composes on one atom.
    pub(super) pending_alias: Option<(String, String)>,
    /// Per-root byte-granular ("hot") regions for mixed-width accesses; kept as per-byte atoms so the sepConj stays satisfiable (H8 Phase B). Computed by the retry loop in `lift_one`.
    pub(super) hot_regions: std::collections::BTreeMap<String, Vec<(i64, i64)>>,
    /// Demotion requests from this pass (wide access over cells outside the current hot set). Merged into `hot_regions` by the retry loop; this pass's output is discarded.
    pub(super) new_hot: Vec<(String, i64, i64)>,
    /// `(root, lo, len, fill)` for constant-count memset blobs; registered by `emit_sol_memset` so later reads can plan a tail split (H8 Phase C).
    pub(super) blobs: Vec<(String, i64, i64, Option<u8>)>,
    /// `(root, lo)` → split offset `n` plan: blob's last 8 bytes (`[n, n+8)`) become a `↦U64` cell. Input to the walk; grown by `new_blob_splits` + retry.
    pub(super) blob_splits: std::collections::BTreeMap<(String, i64), i64>,
    /// Tail-split requests from this pass (dword read at a blob's 8-byte tail); merged by the retry loop.
    pub(super) new_blob_splits: Vec<(String, i64, i64)>,
    /// Per-slot alias equations for the current instruction (a hot wide access whose byte slots live under foreign renderings). Each `(lhs, rhs)` becomes `h_alias_<pc>_<i> : lhs = rhs`, rewritten into the spec hypothesis.
    pub(super) pending_slot_aliases: Vec<(String, String)>,
    /// Post-state value (rendered Lean term) of a `↦Bytes32` atom, keyed by rendered address. Set by `emit_sol_sha256` (output flips to `Sha256.hash inputBytes`); read by `post_atoms`. Default = read-only (pre name unchanged), e.g. `sol_get_sysvar`'s id read.
    pub(super) bytes32_post: std::collections::BTreeMap<String, String>,
    /// Rendered values a syscall spec PINS concretely (e.g. `sol_sha256`'s descriptor `len`), so they must NOT be `generalizing`-abstracted — the hand-written spec call passes them literally and would not match an abstracted goal.
    pub(super) gen_exclude: Vec<String>,
    /// `rr_walk` indices that CONTINUE the previous clause's rr group rather than start a new one. A multi-clause syscall rr (e.g. sha256's `((wOut ∧ rVals) ∧ rPtr)`) must stay a grouped fold-unit so the goal rr matches `sl_block_iter`'s per-instruction (`cuTripleWithinMem_seq`) composition; absent entries default to one-clause-per-group (the flat left-fold, unchanged for existing lifts).
    pub(super) rr_continuations: std::collections::BTreeSet<usize>,
    /// `(hyp_name, prop)` side conditions that REFERENCE blob params (`↦Bytes`/`↦Bytes32` names), e.g. PDA's `pid.size = 32` + off-curve. Emitted in the signature AFTER the blob declarations (unlike `side_hyps`, which precede them and may only reference Nat/register vars), so the forward reference resolves.
    pub(super) blob_side_hyps: Vec<(String, String)>,
}

impl SymState {
    pub(super) fn with_retry_plans(
        hot_regions: std::collections::BTreeMap<String, Vec<(i64, i64)>>,
        blob_splits: std::collections::BTreeMap<(String, i64), i64>,
    ) -> Self {
        Self {
            hot_regions,
            blob_splits,
            ..Self::default()
        }
    }

    pub(super) fn reserve_fresh_name(&self) -> u32 {
        self.names.reserve()
    }

    pub(super) fn alloc_fresh_name(&self) -> u32 {
        self.names.allocate()
    }

    pub(super) fn finish_prepared_step(&self) -> Result<(), LiftError> {
        self.names.finish_prepared_step()
    }

    /// Allocate the per-syscall fresh index plus the `nCu<Tag><idx>` /
    /// `hCu<Tag><idx>` CU-hypothesis names. MUST be called at the same point
    /// in the fresh-name sequence as the emitter's other `*_{idx}` names are
    /// derived — reordering fresh allocations changes emitted binder names.
    pub(super) fn alloc_syscall(&mut self, tag: &str) -> (u32, String, String) {
        let idx = self.alloc_fresh_name();
        (
            idx,
            format!("nCu{}{}", tag, idx),
            format!("hCu{}{}", tag, idx),
        )
    }

    /// Record the byte footprint of a new atom and flag overlap with any DIFFERENT existing atom on the same root. Overlapping atoms in a sepConj → unsatisfiable precondition → vacuous theorem (soundness audit H8).
    pub(super) fn note_access(&mut self, base: &Expr, off: i64, len: i64, key_render: String) {
        let (root, lo) = canon_addr(base, off);
        let hi = lo.wrapping_add(len);
        for (eroot, elo, ehi, ekey) in &self.atom_spans {
            if *eroot == root && *ekey != key_render && lo < *ehi && *elo < hi {
                self.overlap_errors.push(format!(
                    "atom `{key_render}` (root `{root}`, bytes [{lo}, {hi})) \
                     overlaps existing atom `{ekey}` (bytes [{elo}, {ehi}))"
                ));
                return;
            }
        }
        self.atom_spans.push((root, lo, hi, key_render));
    }
    pub(super) fn read_reg(&mut self, r: u8) -> Expr {
        if let Some(v) = self.regs.get(&r) {
            return v.clone();
        }
        let v = Expr::InitReg(reg_initial_name(r));
        self.regs.insert(r, v.clone());
        self.pre.push(Atom::Reg(r, v.clone()));
        v
    }
    pub(super) fn write_reg(&mut self, r: u8, v: Expr) {
        // Record pre-atom before first write so the initial value is captured.
        if let std::collections::btree_map::Entry::Vacant(e) = self.regs.entry(r) {
            let init = Expr::InitReg(reg_initial_name(r));
            e.insert(init.clone());
            self.pre.push(Atom::Reg(r, init));
        }
        self.regs.insert(r, v);
    }
    /// Is `[lo, hi)` on `root` fully inside a hot (byte-demoted) region?
    pub(super) fn hot_covers(&self, root: &str, lo: i64, hi: i64) -> bool {
        self.hot_regions
            .get(root)
            .is_some_and(|v| v.iter().any(|(l, h)| *l <= lo && hi <= *h))
    }
    /// Does `[lo, hi)` on `root` intersect any hot region?
    pub(super) fn hot_intersects(&self, root: &str, lo: i64, hi: i64) -> bool {
        self.hot_regions
            .get(root)
            .is_some_and(|v| v.iter().any(|(l, h)| lo < *h && *l < hi))
    }
    /// The `effectiveAddr …` rendering of a cell (hot byte cells carry
    /// a `+ delta` suffix, matching `ldxdw_bytes_spec`'s atom shape).
    pub(super) fn cell_render(c: &MemCell) -> String {
        if c.delta != 0 {
            format!(
                "effectiveAddr ({}) ({}) + {}",
                c.addr_base.to_lean(),
                c.addr_off,
                c.delta
            )
        } else {
            format!("effectiveAddr ({}) ({})", c.addr_base.to_lean(), c.addr_off)
        }
    }
    /// Push a `new_hot` request covering the UNION of `[lo, lo+wlen)` and every conflicting cell's span when footprints conflict or straddle a hot edge (but NOT for same span+width, which is the aliased lookup's job).
    pub(super) fn request_demotion_on_conflict(
        &mut self,
        root: &str,
        lo: i64,
        wlen: i64,
        width: Width,
    ) {
        let (mut nlo, mut nhi) = (lo, lo + wlen);
        let mut conflict = false;
        for c in &self.mem {
            let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
            if cr != root {
                continue;
            }
            let cl = cd + c.delta;
            let ch = cl
                + match c.width {
                    Width::Byte => 1,
                    Width::Halfword => 2,
                    Width::Word => 4,
                    Width::Dword => 8,
                };
            let same_cell = cl == lo && ch == lo + wlen && c.width as u8 == width as u8;
            if !same_cell && lo < ch && cl < lo + wlen {
                conflict = true;
                nlo = nlo.min(cl);
                nhi = nhi.max(ch);
            }
        }
        if conflict || self.hot_intersects(root, lo, lo + wlen) {
            self.new_hot.push((root.to_string(), nlo, nhi));
        }
    }
    /// Address rendering `*_bytes_spec` uses for slot `k` of access at `(base, off)`.
    pub(super) fn slot_expected_render(base: &Expr, off: i64, k: i64) -> String {
        if k == 0 {
            format!("effectiveAddr ({}) ({})", base.to_lean(), off)
        } else {
            format!("effectiveAddr ({}) ({}) + {}", base.to_lean(), off, k)
        }
    }
    /// Resolve or materialize the byte cell for slot `k` of a hot wide access. Foreign-rendered slots get a per-slot alias equation in `pending_slot_aliases`.
    pub(super) fn hot_slot(&mut self, base_expr: &Expr, off: i64, k: i64) -> usize {
        let (root, lo) = canon_addr(base_expr, off);
        let base_lean = base_expr.to_lean();
        if let Some(i) = self.mem.iter().position(|c| {
            matches!(c.width, Width::Byte) && {
                let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                cr == root && cd + c.delta == lo + k
            }
        }) {
            let render_ok = self.mem[i].addr_base.to_lean() == base_lean
                && self.mem[i].addr_off == off
                && ((k == 0 && self.mem[i].delta == 0) || self.mem[i].delta == k);
            if !render_ok {
                self.pending_slot_aliases.push((
                    Self::cell_render(&self.mem[i]),
                    Self::slot_expected_render(base_expr, off, k),
                ));
            }
            // Bare vars in wide-access byte slots need a `< 256` bound.
            if let Expr::InitMem(name) = &self.mem[i].value {
                let name = name.clone();
                if !self.u64_load_vars.iter().any(|(n, _)| *n == name) {
                    self.u64_load_vars.push((name, 8));
                }
            }
            return i;
        }
        let idx = self.alloc_fresh_name();
        let name = format!("oldMemB_{}", idx);
        self.u64_load_vars.push((name.clone(), 8));
        let v = Expr::InitMem(name);
        self.mem.push(MemCell {
            addr_base: base_expr.clone(),
            addr_off: off,
            width: Width::Byte,
            value: v.clone(),
            delta: k,
        });
        self.pre.push(Atom::Mem {
            addr_base: base_expr.clone(),
            addr_off: off,
            width: Width::Byte,
            value: v,
            delta: k,
        });
        self.note_access(
            base_expr,
            off + k,
            1,
            format!("{}@{}+{}:HotByte", base_lean, off, k),
        );
        self.mem.len() - 1
    }
    /// Hot `st .word imm`: realize 4 byte cells (pre = spec's `b0..b3`) and overwrite with LE bytes of `imm` (`stw_bytes_spec`'s `c0..c3`).
    pub(super) fn write_hot_word_imm(&mut self, base_expr: Expr, off: i64, imm: i64) {
        let w = imm as u32; // toU64 imm % 2^32
        let bytes = w.to_le_bytes();
        for k in 0..4i64 {
            let i = self.hot_slot(&base_expr, off, k);
            self.mem[i].value = Expr::Const(bytes[k as usize] as i64);
        }
        self.rr_walk.push((base_expr, off, Width::Word, true, None));
    }
    /// Serve a hot wide LOAD: reuse/materialize 8 byte cells and return their Horner combination (matches `ldxdw_bytes_spec`). Fail-closed for non-dword widths.
    pub(super) fn read_hot_wide(&mut self, base_expr: Expr, off: i64, width: Width) -> Expr {
        if !matches!(width, Width::Dword) {
            self.overlap_errors.push(format!(
                "hot-region {:?} access at ({})+{} — only dword LOADS are \
                 byte-demoted so far (H8 Phase B-1)",
                width,
                base_expr.to_lean(),
                off
            ));
            return Expr::Raw("hotUnsupported".into());
        }
        let mut vals: Vec<Expr> = Vec::with_capacity(8);
        for k in 0..8i64 {
            let i = self.hot_slot(&base_expr, off, k);
            vals.push(self.mem[i].value.clone());
        }
        self.rr_walk
            .push((base_expr, off, Width::Dword, false, None));
        Expr::ByteCombo(vals)
    }
    /// Exact-rendering lookup first, then canonical `(root, disp, width)` — a canonical hit is the SAME cell under a different rendering (Phase A aliasing). Returns `(index, is_alias)`.
    pub(super) fn lookup_cell_aliased(
        &self,
        base: &Expr,
        off: i64,
        width: Width,
    ) -> Option<(usize, bool)> {
        let key = (base.to_lean(), off, 0i64, width as u8);
        if let Some(i) = self.mem.iter().position(|c| c.key() == key) {
            return Some((i, false));
        }
        let (root, disp) = canon_addr(base, off);
        self.mem
            .iter()
            .position(|c| {
                if c.width as u8 != width as u8 {
                    return false;
                }
                let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                cr == root && cd + c.delta == disp
            })
            .map(|i| (i, true))
    }
    pub(super) fn read_mem(&mut self, base: u8, off: i64, width: Width) -> Expr {
        let base_expr = self.read_reg(base);
        let wlen = match width {
            Width::Byte => 1i64,
            Width::Halfword => 2,
            Width::Word => 4,
            Width::Dword => 8,
        };
        if wlen > 1 {
            let (root, lo) = canon_addr(&base_expr, off);
            // Dword read at blob's 8-byte tail → plan a tail split (`↦U64` cell, H8 Phase C). New: request + retry; already planned: aliased lookup hits below.
            if matches!(width, Width::Dword) {
                if let Some((broot, blo, blen, _)) = self
                    .blobs
                    .iter()
                    .find(|(br, bl, bn, _)| *br == root && *bl <= lo && lo + 8 <= *bl + *bn)
                    .cloned()
                {
                    let rel = lo - blo;
                    if rel + 8 == blen && !self.blob_splits.contains_key(&(broot.clone(), blo)) {
                        self.new_blob_splits.push((broot, blo, rel));
                    }
                    // Non-tail reads fall through to the overlap detector (middle split not implemented).
                }
            }
            if self.hot_covers(&root, lo, lo + wlen) {
                return self.read_hot_wide(base_expr, off, width);
            }
            // Footprint conflict or hot-edge straddle: request demotion and retry (this pass's output is discarded).
            self.request_demotion_on_conflict(&root, lo, wlen, width);
        }
        if let Some((i, aliased)) = self.lookup_cell_aliased(&base_expr, off, width) {
            let cell_base = self.mem[i].addr_base.clone();
            let cell_off = self.mem[i].addr_off;
            let v = self.mem[i].value.clone();
            // Every load instruction, even a re-read, contributes `containsRange` to keep the goal rr 1:1 with walked instructions.
            if aliased {
                // Aliased: rr clause and (via `rw [h_alias_<pc>]`) the spec hypothesis use the CANONICAL rendering — one atom per physical cell.
                let rhs = Self::cell_render(&self.mem[i]);
                self.pending_alias = Some((
                    format!("effectiveAddr ({}) ({})", base_expr.to_lean(), off),
                    rhs,
                ));
                self.rr_walk.push((cell_base, cell_off, width, false, None));
            } else {
                self.rr_walk.push((base_expr, off, width, false, None));
            }
            return v;
        }
        // Name fresh cells by width+index; the address expression itself may be ill-suited as a Lean identifier.
        let idx = self.alloc_fresh_name();
        let name = format!("oldMem{}_{}", w_short(width), idx);
        match width {
            Width::Dword => self.u64_load_vars.push((name.clone(), 64)),
            Width::Word => self.u64_load_vars.push((name.clone(), 32)),
            Width::Halfword => self.u64_load_vars.push((name.clone(), 16)),
            Width::Byte => {} // bytes always fit; no bound needed
        }
        let v = Expr::InitMem(name);
        let cell = MemCell {
            addr_base: base_expr.clone(),
            addr_off: off,
            width,
            value: v.clone(),
            delta: 0,
        };
        let width_len = match width {
            Width::Byte => 1,
            Width::Halfword => 2,
            Width::Word => 4,
            Width::Dword => 8,
        };
        self.note_access(
            &base_expr,
            off,
            width_len,
            format!("{}@{}:{:?}", base_expr.to_lean(), off, width),
        );
        self.mem.push(cell);
        self.pre.push(Atom::Mem {
            addr_base: base_expr.clone(),
            addr_off: off,
            width,
            value: v.clone(),
            delta: 0,
        });
        self.rr_walk.push((base_expr, off, width, false, None));
        v
    }
    pub(super) fn write_mem(&mut self, base: u8, off: i64, width: Width, value: Expr) {
        let base_expr = self.read_reg(base);
        let wlen = match width {
            Width::Byte => 1i64,
            Width::Halfword => 2,
            Width::Word => 4,
            Width::Dword => 8,
        };
        if wlen > 1 {
            let (root, lo) = canon_addr(&base_expr, off);
            if self.hot_covers(&root, lo, lo + wlen) {
                // Only word-immediate stores are byte-demotable (`stw_bytes_spec`); other wide hot stores fail closed.
                if matches!(width, Width::Word) {
                    if let Expr::StWordImm(imm) = &value {
                        let imm = *imm;
                        self.write_hot_word_imm(base_expr, off, imm);
                        return;
                    }
                }
                self.overlap_errors.push(format!(
                    "wide {:?} STORE at ({})+{} into a hot (byte-demoted) \
                     region — only word-immediate stores and dword loads \
                     are supported so far (H8 Phase B)",
                    width,
                    base_expr.to_lean(),
                    off
                ));
                return;
            }
            self.request_demotion_on_conflict(&root, lo, wlen, width);
            if self.hot_intersects(&root, lo, lo + wlen) {
                // Straddles a hot edge without full coverage — the
                // demotion request above will widen the region; this
                // pass is discarded.
                return;
            }
        }
        // Materialize the pre-atom if missing (store without preceding load). Canon-aware: avoids creating an overlapping twin (Phase A aliasing).
        if self.lookup_cell_aliased(&base_expr, off, width).is_none() {
            let _ = self.read_mem(base, off, width);
            // `read_mem` pushed a `containsRange` entry, but this is a STORE: drop it so the goal rr stays 1:1 with memory instructions (containsWritable below implies readability).
            self.rr_walk.pop();
        }
        if let Some((i, aliased)) = self.lookup_cell_aliased(&base_expr, off, width) {
            let cell_base = self.mem[i].addr_base.clone();
            let cell_off = self.mem[i].addr_off;
            self.mem[i].value = value;
            if aliased {
                let rhs = Self::cell_render(&self.mem[i]);
                self.pending_alias = Some((
                    format!("effectiveAddr ({}) ({})", base_expr.to_lean(), off),
                    rhs,
                ));
                self.rr_walk.push((cell_base, cell_off, width, true, None));
            } else {
                self.rr_walk.push((base_expr, off, width, true, None));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_names_reserve_once_and_consume_in_order() {
        let names = FreshNames::default();
        assert_eq!(names.reserve(), 0);
        assert_eq!(names.reserve(), 1);
        assert_eq!(names.allocate(), 0);
        assert_eq!(names.allocate(), 1);
        names
            .finish_prepared_step()
            .expect("all reservations consumed");
        assert_eq!(names.allocate(), 2);
    }

    #[test]
    fn unused_fresh_name_reservation_fails_closed() {
        let names = FreshNames::default();
        names.reserve();
        let error = names
            .finish_prepared_step()
            .expect_err("unused reservation must fail");
        assert_eq!(error.kind(), DiagnosticKind::Other);
    }
}
