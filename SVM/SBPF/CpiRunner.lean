/-
  The runner's CPI invoke step as a `Cpi.applyResult` transition.

  `Runner.stepCpi` is the per-instruction step of `executeFnCpiWithFuel`
  with the callee's sub-run as a parameter. Every branch of an invoke
  (`sol_invoke_signed{,_c}`) — depth limit, writable aliasing, native
  dispatch, unregistered program, failed callee build, BPF sub-run — commits
  through `applyResult` once the caller's per-step CU (`chargeCu`) is folded
  into the result's `cuConsumed` (`stepCpi_is_transition`).

  `runnerCallee registry sc` is the callee relation the concrete runner
  induces: the results `r` for which some fuel makes the charged invoke step
  equal `applyResult s r`.
-/

import SVM.SBPF.Runner
import SVM.SBPF.RunnerBridge
import SVM.SBPF.CpiContract
import SVM.SBPF.CpiSerialization

namespace SVM.SBPF
namespace Cpi

/-- The callee relation the runner induces for invoke syscall `sc`. -/
def runnerCallee (registry : Nat → Option ByteArray) (sc : Syscall) : CalleeSemantics :=
  fun s r => ∃ fuel',
    chargeCu (Runner.stepCpi registry (Runner.executeFnCpiWithFuel registry) s fuel' (.call sc))
      = applyResult s r

/-- `chargeCu` after a commit is a commit with one more callee CU. -/
theorem chargeCu_applyResult (s : State) (r : CalleeResult) :
    chargeCu (applyResult s r) = applyResult s { r with cuConsumed := r.cuConsumed + 1 } := by
  simp only [chargeCu, applyResult, Nat.add_assoc]

/-- The fail-closed invoke arms (r0 := 1, no memory change) are commits of an
    error result carrying the caller's own channels. -/
theorem chargeCu_invokeFail (s : State) :
    chargeCu { s with regs := s.regs.set .r0 1, pc := s.pc + 1,
                      cuConsumed := s.cuConsumed + Cpi.cu }
      = applyResult s ⟨1, s.mem, s.log, s.returnData, s.returnDataProgId, 1⟩ := by
  simp only [chargeCu, applyResult, Nat.one_ne_zero, if_false]

/-- Every branch of `cpiCallNextState` on an invoke syscall, charged its
    per-step CU, is an `applyResult` commit, for any callee runner.
    `extract_lets` keeps the heavy lets (pid fold, account parsers) opaque so
    `split` sees only the five structural branches (as in
    `cpiCallNextState_bounded`). -/
theorem cpiCallNextState_is_transition (registry : Nat → Option ByteArray) (s : State)
    (sc : Syscall) (fuel' : Nat) (runCallee : ByteArray → Option (State × Memory.Mem × Nat))
    (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c) :
    ∃ r, chargeCu (Runner.cpiCallNextState registry s sc fuel' runCallee) = applyResult s r := by
  rcases hsc with rfl | rfl <;>
    (unfold Runner.cpiCallNextState
     extract_lets
     repeat' split
     all_goals
       first
         | exact ⟨_, chargeCu_invokeFail s⟩
         | exact ⟨_, chargeCu_applyResult _ _⟩)

/-- Every branch of the runner's invoke step is an `applyResult` transition.
    Witnesses: fail-closed arms (depth, aliasing, unregistered, failed callee
    build) `⟨1, s.mem, s.log, s.returnData, s.returnDataProgId, 1⟩`; native
    `⟨nr.r0, nr.mem, s.log, s.returnData, s.returnDataProgId, nr.cu + 1⟩`;
    BPF `⟨subFinal.exitCode.getD 1, newMem, subFinal.log, subFinal.returnData,
    subFinal.returnDataProgId, subFinal.cuConsumed + 1⟩`. The `+ 1` is
    `chargeCu`'s per-step unit. -/
theorem stepCpi_is_transition (registry : Nat → Option ByteArray)
    (subRun : (Nat → Option Insn) → State → Nat → State × Nat) (s : State) (fuel' : Nat)
    (sc : Syscall) (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c) :
    ∃ r, chargeCu (Runner.stepCpi registry subRun s fuel' (.call sc)) = applyResult s r := by
  -- `extract_lets` keeps the ABI decoding lets opaque; a bare `exact` makes
  -- the unifier whnf them and times out on the C arm.
  rcases hsc with rfl | rfl <;>
    (unfold Runner.stepCpi
     extract_lets
     exact cpiCallNextState_is_transition registry s _ fuel' _ (by simp))

/-! ## Running the runner through an invoke

`executeFn`'s `step` treats an invoke as the fail-closed `Cpi.exec`: it sets
`exitCode`, and halts are sticky. So an `executeFn` run that ends live
(`exitCode = none`) never executed an invoke, and on such a run the runner
(`executeFnCpiWithFuel`) takes exactly the same steps (`runner_prefix`). The
invoke itself is one runner step (`runner_invoke`) whose charged result is an
`applyResult` commit (`stepCpi_is_transition`). `runner_cpiPath` glues these
to a `cpiPathWithinMem` path: prefix, invoke, suffix, then the runner
continues from the suffix's end state. -/

/-- A non-invoke instruction's CPI-aware step is the ordinary `step`. -/
theorem stepCpi_of_not_cpi (registry : Nat → Option ByteArray)
    (subRun : (Nat → Option Insn) → State → Nat → State × Nat) (s : State) (fuel' : Nat)
    (insn : Insn) (h : Insn.isCpiCall insn = false) :
    Runner.stepCpi registry subRun s fuel' insn = step insn s := by
  cases insn with
  | call sc => cases sc <;> first | rfl | (simp [Insn.isCpiCall] at h)
  | _ => rfl

/-- Under `executeFn`, an invoke halts (`Cpi.exec` is fail-closed). -/
theorem chargeCu_step_invoke_exitCode (insn : Insn) (s : State)
    (h : Insn.isCpiCall insn = true) :
    (chargeCu (step insn s)).exitCode = some ERR_UNSUPPORTED_INSTRUCTION := by
  cases insn with
  | call sc =>
    cases sc <;> first
      | rfl
      | (simp [Insn.isCpiCall] at h)
  | _ => simp [Insn.isCpiCall] at h

/-- The runner agrees with `executeFn` on any run that ends live and within
    budget: such a run never faulted, never executed an invoke (that would
    halt it) and never hit the budget halt (a fixed point, so the end state
    would be over budget). The runner then continues from the end state with
    the leftover fuel. -/
theorem runner_prefix (registry : Nat → Option ByteArray) (fetch : Nat → Option Insn) :
    ∀ (k : Nat) (s : State) (m : Nat),
      (executeFn fetch s k).exitCode = none →
      ¬ (executeFn fetch s k).cuConsumed > (executeFn fetch s k).cuBudget →
      Runner.executeFnCpiWithFuel registry fetch s (k + m) =
        Runner.executeFnCpiWithFuel registry fetch (executeFn fetch s k) m
  | 0, s, m, _, _ => by rw [Nat.zero_add, executeFn_zero]
  | k + 1, s, m, hex, hbud => by
    cases hs : s.exitCode with
    | some c =>
      rw [executeFn_halted fetch s _ c hs, hs] at hex
      cases hex
    | none =>
      by_cases hov : s.cuConsumed > s.cuBudget
      · rw [executeFn_overBudget fetch s _ hs hov] at hbud
        exact absurd hov hbud
      · cases hf : fetch s.pc with
        | none =>
          simp only [executeFn, hs, if_neg hov, hf] at hex
          cases hex
        | some insn =>
          rw [executeFn_step fetch s k insn hs (Nat.le_of_not_lt hov) hf] at hex hbud ⊢
          cases hc : Insn.isCpiCall insn
          · rw [show k + 1 + m = (k + m) + 1 by omega,
              Runner.executeFnCpiWithFuel_succ_insn registry fetch s (k + m) insn hs hov hf,
              stepCpi_of_not_cpi _ _ _ _ _ hc]
            exact runner_prefix registry fetch k _ m hex hbud
          · rw [executeFn_halted fetch _ k _ (chargeCu_step_invoke_exitCode insn s hc)] at hex
            rw [chargeCu_step_invoke_exitCode insn s hc] at hex
            cases hex

/-- One runner step at a live, in-budget invoke: the charged `stepCpi`
    successor, with the sub-run at the remaining fuel `m`. -/
theorem runner_invoke (registry : Nat → Option ByteArray) (fetch : Nat → Option Insn)
    (sI : State) (sc : Syscall) (m : Nat)
    (hex : sI.exitCode = none) (hbud : sI.cuConsumed ≤ sI.cuBudget)
    (hf : fetch sI.pc = some (.call sc)) :
    Runner.executeFnCpiWithFuel registry fetch sI (m + 1) =
      Runner.executeFnCpiWithFuel registry fetch
        (chargeCu (Runner.stepCpi registry (Runner.executeFnCpiWithFuel registry) sI m (.call sc)))
        m :=
  Runner.executeFnCpiWithFuel_succ_insn registry fetch sI m _ hex (Nat.not_lt.mpr hbud) hf

/-- From a live state at an invoke, `executeFn` either stays put (budget
    halt) or halts. -/
private theorem executeFn_from_invoke (fetch : Nat → Option Insn) (t : State) (sc : Syscall)
    (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hex : t.exitCode = none) (hf : fetch t.pc = some (.call sc)) :
    ∀ d, executeFn fetch t d = t ∨ (executeFn fetch t d).exitCode ≠ none
  | 0 => Or.inl (executeFn_zero fetch t)
  | d + 1 => by
    by_cases hov : t.cuConsumed > t.cuBudget
    · exact Or.inl (executeFn_overBudget fetch t _ hex hov)
    · have hcpi : Insn.isCpiCall (.call sc) = true := by
        rcases hsc with rfl | rfl <;> rfl
      right
      rw [executeFn_step fetch t d _ hex (Nat.le_of_not_lt hov) hf,
        executeFn_halted fetch _ d _ (chargeCu_step_invoke_exitCode _ t hcpi),
        chargeCu_step_invoke_exitCode _ t hcpi]
      simp

/-- The live invoke state of an `executeFn` run is unique: running on from a
    live invoke either halts or stays put, so any two live visits to the
    invoke pc are the same state. -/
theorem executeFn_invoke_unique (fetch : Nat → Option Insn) (s : State) (invokePc : Nat)
    (sc : Syscall) (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hf : fetch invokePc = some (.call sc)) {a b : Nat}
    (ha : (executeFn fetch s a).pc = invokePc) (hae : (executeFn fetch s a).exitCode = none)
    (hb : (executeFn fetch s b).pc = invokePc) (hbe : (executeFn fetch s b).exitCode = none) :
    executeFn fetch s a = executeFn fetch s b := by
  have key : ∀ {x y : Nat}, x ≤ y → (executeFn fetch s x).pc = invokePc →
      (executeFn fetch s x).exitCode = none → (executeFn fetch s y).exitCode = none →
      executeFn fetch s x = executeFn fetch s y := by
    intro x y hxy hx hxe hye
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [executeFn_compose] at hye ⊢
    rcases executeFn_from_invoke fetch _ sc hsc hxe (hx ▸ hf) d with h | h
    · exact h.symm
    · exact absurd hye h
  rcases Nat.le_total a b with h | h
  · exact key h ha hae hbe
  · exact (key h hb hbe hae).symm

/-- Discharge the reached-state invariant hypothesis of `runnerCpiPath` from
    a prefix triple ending at the invoke: `inv` follows from the prefix post
    (framed by `R`) at the unique live invoke state. -/
theorem inv_of_prefix {N1 M1 entry invokePc : Nat} {cr1 : CodeReq} {P Q R : Assertion}
    {rr1 : Memory.RegionTable → Prop} {sc : Syscall} {inv : State → Prop}
    (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hPre : cuTripleWithinMem N1 M1 entry invokePc cr1 P Q rr1)
    (hInvQ : ∀ sI, (Q ** R).holdsFor sI → inv sI)
    (hR : R.pcFree) (fetch : Nat → Option Insn) (hcr1 : cr1.SatisfiedBy fetch)
    (hf : fetch invokePc = some (.call sc))
    (s : State) (hP : (P ** R).holdsFor s) (hpc : s.pc = entry) (hex : s.exitCode = none)
    (hbud : s.cuConsumed + N1 + M1 ≤ s.cuBudget) (hrr1 : rr1 s.regions) :
    ∀ k, (executeFn fetch s k).pc = invokePc → (executeFn fetch s k).exitCode = none →
      inv (executeFn fetch s k) := by
  intro k hk hke
  obtain ⟨k0, _, hpc0, hex0, _, hQ⟩ := hPre R hR fetch hcr1 s hP hpc hex hbud hrr1
  rw [executeFn_invoke_unique fetch s invokePc sc hsc hf hk hke hpc0 hex0]
  exact hInvQ _ hQ

/-- The runner-level reading of a CPI path: for fuel `F` covering the path,
    the runner's invoke state `sI := executeFn fetch s k1` (reached within
    `N1` steps), the result `r` the runner's invoke step commits at sub-run
    fuel `F - k1 - 1` (admitted by the restricted runner callee), and, when
    `r` passes the guard and the suffix budget, the suffix end state
    `sE := executeFn fetch (applyResult sI r) k2` at `exit_` in `Post r ** R`,
    from which the runner continues with fuel `F - k1 - 1 - k2`.

    `inv` must hold at every live visit to `invokePc`; there is only one
    (`executeFn_invoke_unique`), and `inv_of_prefix` discharges it from a
    prefix triple. -/
def runnerCpiPath (registry : Nat → Option ByteArray) (N1 M1 entry invokePc N2 M2 exit_ : Nat)
    (cr1 cr2 : CodeReq) (P : Assertion) (Post : CalleeResult → Assertion)
    (rr1 rr2 : Memory.RegionTable → Prop) (sc : Syscall) (inv : State → Prop)
    (G : CalleeResult → Prop) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn),
    (cr1.union (CodeReq.singleton invokePc (.call sc))).SatisfiedBy fetch →
    cr2.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + N1 + M1 ≤ s.cuBudget → rr1 s.regions → rr2 s.regions →
    (∀ k, (executeFn fetch s k).pc = invokePc → (executeFn fetch s k).exitCode = none →
      inv (executeFn fetch s k)) →
  ∀ (F : Nat), N1 + 1 + N2 ≤ F →
    ∃ k1, k1 ≤ N1 ∧
      (executeFn fetch s k1).pc = invokePc ∧
      (executeFn fetch s k1).exitCode = none ∧
      ∃ r, restrict (runnerCallee registry sc) inv (executeFn fetch s k1) r ∧
        chargeCu (Runner.stepCpi registry (Runner.executeFnCpiWithFuel registry)
            (executeFn fetch s k1) (F - k1 - 1) (.call sc))
          = applyResult (executeFn fetch s k1) r ∧
        (G r →
          (applyResult (executeFn fetch s k1) r).cuConsumed + N2 + M2 ≤
            (applyResult (executeFn fetch s k1) r).cuBudget →
          ∃ k2, k2 ≤ N2 ∧
            (executeFn fetch (applyResult (executeFn fetch s k1) r) k2).pc = exit_ ∧
            (executeFn fetch (applyResult (executeFn fetch s k1) r) k2).exitCode = none ∧
            (executeFn fetch (applyResult (executeFn fetch s k1) r) k2).cuConsumed ≤
              (applyResult (executeFn fetch s k1) r).cuConsumed + N2 + M2 ∧
            (Post r ** R).holdsFor (executeFn fetch (applyResult (executeFn fetch s k1) r) k2) ∧
            Runner.executeFnCpiWithFuel registry fetch s F =
              Runner.executeFnCpiWithFuel registry fetch
                (executeFn fetch (applyResult (executeFn fetch s k1) r) k2) (F - k1 - 1 - k2))

/-- A caller path across one invoke, proved against the runner's own callee
    relation (restricted to `inv`), holds of the runner itself. -/
theorem runner_cpiPath {N1 M1 entry invokePc N2 M2 exit_ : Nat} {cr1 cr2 : CodeReq}
    {P : Assertion} {Post : CalleeResult → Assertion} {rr1 rr2 : Memory.RegionTable → Prop}
    {sc : Syscall} {inv : State → Prop} {G : CalleeResult → Prop}
    (registry : Nat → Option ByteArray)
    (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hPath : cpiPathWithinMem N1 M1 entry invokePc N2 M2 exit_ cr1 cr2 P Post rr1 rr2 sc
      (restrict (runnerCallee registry sc) inv) G) :
    runnerCpiPath registry N1 M1 entry invokePc N2 M2 exit_ cr1 cr2 P Post rr1 rr2 sc inv G := by
  intro R hR fetch hcr1 hcr2 s hP hpc hex hbud hrr1 hrr2 hInv F hF
  obtain ⟨k1, hk1, hpc1, hfI, hex1, hT⟩ :=
    hPath R hR fetch hcr1 hcr2 s hP hpc hex hbud hrr1 hrr2
  obtain ⟨r0, hr0⟩ := stepCpi_is_transition registry (Runner.executeFnCpiWithFuel registry)
    (executeFn fetch s k1) (F - k1 - 1) sc hsc
  have hTr : Transitions (restrict (runnerCallee registry sc) inv) (executeFn fetch s k1)
      (applyResult (executeFn fetch s k1) r0) :=
    ⟨r0, ⟨hInv k1 hpc1 hex1, F - k1 - 1, hr0⟩, rfl⟩
  obtain ⟨r, hr, hs', hSuf⟩ := hT _ hTr
  rw [hs'] at hSuf
  refine ⟨k1, hk1, hpc1, hex1, r, hr, hr0.trans hs', fun hG hbud2 => ?_⟩
  obtain ⟨k2, hk2, hpc2, hex2, hcu2, hPost⟩ := hSuf hG hbud2
  refine ⟨k2, hk2, hpc2, hex2, hcu2, hPost, ?_⟩
  have hIbud : (executeFn fetch s k1).cuConsumed ≤ (executeFn fetch s k1).cuBudget := by
    simp only [applyResult] at hbud2; omega
  have hEbud : ¬ (executeFn fetch (applyResult (executeFn fetch s k1) r) k2).cuConsumed >
      (executeFn fetch (applyResult (executeFn fetch s k1) r) k2).cuBudget := by
    rw [executeFn_preserves_cuBudget]; omega
  calc Runner.executeFnCpiWithFuel registry fetch s F
      = Runner.executeFnCpiWithFuel registry fetch s (k1 + ((F - k1 - 1) + 1)) := by
        congr 1; omega
    _ = Runner.executeFnCpiWithFuel registry fetch (executeFn fetch s k1) ((F - k1 - 1) + 1) :=
        runner_prefix registry fetch k1 s _ hex1 (Nat.not_lt.mpr hIbud)
    _ = Runner.executeFnCpiWithFuel registry fetch
          (applyResult (executeFn fetch s k1) r) (k2 + (F - k1 - 1 - k2)) := by
        rw [runner_invoke registry fetch _ sc _ hex1 hIbud (hpc1 ▸ hfI), hr0, hs']
        congr 1; omega
    _ = _ := runner_prefix registry fetch k2 _ _ hex2 hEbud

/-! ## Generic write-back frame -/

/-- The parsed, PDA-promoted, privilege-clamped account infos the runner's
    invoke step hands the callee at `s` (both ABIs). -/
def invokeAccts (s : State) (sc : Syscall) : List Runner.ParsedAcct :=
  let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
  let parsedAcctsRaw : List Runner.ParsedAcct :=
    match sc with
    | .sol_invoke_signed_c => Runner.parseCpiAccounts s.mem s.regs.r2 accountCount
    | _ => Runner.parseAccountInfos s.mem s.regs.r2 accountCount
  Runner.clampCpiPrivileges parsedAcctsRaw
    (Runner.deriveSignerPdas s.mem s.regs.r4 s.regs.r5 s.progIdBytes) s.origPrivs

/-- The slot table the runner builds for the callee at `s`. -/
def invokeSlots (s : State) (sc : Syscall) : List Runner.AcctSlot :=
  Runner.buildAcctSlots (invokeAccts s sc)

/-- The program id `cpiCallNextState` computes at `s` (four LE u64 limbs). -/
def invokePid (s : State) (sc : Syscall) : Nat :=
  let pubkeyAddr : Nat := match sc with
    | .sol_invoke_signed   => s.regs.r1 + 48
    | .sol_invoke_signed_c => Memory.readU64 s.mem s.regs.r1
    | _ => s.regs.r1
  Memory.readU64 s.mem pubkeyAddr
    + Memory.readU64 s.mem (pubkeyAddr + 8) * 2 ^ 64
    + Memory.readU64 s.mem (pubkeyAddr + 16) * 2 ^ 128
    + Memory.readU64 s.mem (pubkeyAddr + 24) * 2 ^ 192

/-- The instruction data `cpiCallNextState` hands native dispatch. -/
def invokeIxData (s : State) (sc : Syscall) : ByteArray :=
  let ixDataPtr : Nat := Memory.readU64 s.mem (s.regs.r1 + 24)
  let ixDataLen : Nat := match sc with
    | .sol_invoke_signed   => Memory.readU64 s.mem (s.regs.r1 + 40)
    | .sol_invoke_signed_c => Memory.readU64 s.mem (s.regs.r1 + 32)
    | _ => 0
  Runner.readMemBytes s.mem ixDataPtr ixDataLen

/-- The native-program view of the invoke's accounts. -/
def invokeNativeAccts (s : State) (sc : Syscall) : List SVM.Native.AcctInput :=
  (invokeAccts s sc).map (fun p =>
    { key := p.key, owner := p.owner, lamports := p.lamports,
      dataLen := p.dataLen, isSigner := p.isSigner,
      isWritable := p.isWritable,
      lamportsRefAddr := p.lamportsRefAddr,
      ownerPtr := p.ownerPtr, dataPtr := p.dataPtr,
      dataLenRefAddr := p.dataLenRefAddr })

/-- The invoke does not dispatch to a native program. -/
def invokeNativeNone (s : State) (sc : Syscall) : Prop :=
  SVM.Native.dispatch (invokePid s sc) (invokeIxData s sc) (invokeNativeAccts s sc) s.mem = none

/-- The caller bytes the runner's write-back may touch for the invoke at `s`. -/
def invokeFootprint (s : State) (sc : Syscall) (a : Nat) : Prop :=
  Runner.writeBackFootprint (invokeSlots s sc) a

/-- Outside `fp`, every non-native branch of `cpiCallNextState` leaves caller
    memory unchanged, given that any successful callee run does. -/
theorem cpiCallNextState_mem_frame (registry : Nat → Option ByteArray) (s : State)
    (sc : Syscall) (fuel' : Nat) (runCallee : ByteArray → Option (State × Memory.Mem × Nat))
    (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hN : invokeNativeNone s sc) (fp : Nat → Prop)
    (hRC : ∀ elf t m f, runCallee elf = some (t, m, f) → ∀ a, ¬ fp a → m a = s.mem a)
    (a : Nat) (ha : ¬ fp a) :
    (Runner.cpiCallNextState registry s sc fuel' runCallee).mem a = s.mem a := by
  rcases hsc with rfl | rfl <;>
    (unfold Runner.cpiCallNextState
     extract_lets
     repeat' split
     all_goals first
       | rfl
       | (rename_i hrun
          show (if _ = 0 then _ else s.mem) a = s.mem a
          split
          · exact hRC _ _ _ _ hrun a ha
          · rfl)
       | (rename_i hnat
          have hN' := hN
          unfold invokeNativeNone at hN'
          exact absurd (hnat.symm.trans hN') (Option.some_ne_none _)))


/-- The runner's invoke step (any sub-run) changes caller memory only inside
    the invoke's write-back footprint, when the program id is not native. -/
theorem stepCpi_mem_frame (registry : Nat → Option ByteArray)
    (subRun : (Nat → Option Insn) → State → Nat → State × Nat) (s : State) (fuel' : Nat)
    (sc : Syscall) (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hN : invokeNativeNone s sc) (a : Nat) (ha : ¬ invokeFootprint s sc a) :
    (Runner.stepCpi registry subRun s fuel' (.call sc)).mem a = s.mem a := by
  rcases hsc with rfl | rfl <;>
    (unfold Runner.stepCpi
     extract_lets runCallee
     refine cpiCallNextState_mem_frame registry s _ fuel' _ (by simp) hN
       (invokeFootprint s _) ?_ a ha
     intro elf t m f h b hb
     simp only [runCallee, bind, Option.bind_eq_some_iff] at h
     obtain ⟨⟨insns, subS, slots⟩, hbuild, h⟩ := h
     simp only [Option.some.injEq] at h
     have hm := congrArg (fun x : State × Memory.Mem × Nat => x.2.1) h
     simp only at hm
     rw [← hm, Runner.buildCalleeVM_slots hbuild]
     exact Runner.commitCallee_mem_outside _ _ _ _ _ hb)

/-- Generic write frame: every successful result of the runner's callee
    relation for a BPF callee differs from caller memory only inside the
    write-back footprint of the accounts parsed at the invoke. Stated
    pointwise because the footprint depends on `s`. -/
theorem runnerCallee_writesWithin (registry : Nat → Option ByteArray) (sc : Syscall)
    (inv : State → Prop) (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hNative : ∀ s, inv s → invokeNativeNone s sc) :
    ∀ s r, restrict (runnerCallee registry sc) inv s r → r.code = 0 →
      ∀ a, ¬ invokeFootprint s sc a → r.mem a = s.mem a := by
  rintro s r ⟨hinv, fuel', hr⟩ hc a ha
  have h := congrArg (fun t => t.mem a) hr
  simp only [chargeCu, applyResult, hc, if_true] at h
  rw [← h]
  exact stepCpi_mem_frame registry _ s fuel' sc hsc (hNative s hinv) a ha

/-! ## The successful BPF arm

A zero `r0` after an invoke (non-native) pins the BPF arm: the program id is
registered, the callee built and ran, and caller memory is the commit's. -/

/-- Code 0 after a non-native invoke comes from the registered-BPF arm. -/
theorem cpiCallNextState_success (registry : Nat → Option ByteArray) (s : State)
    (sc : Syscall) (fuel' : Nat) (runCallee : ByteArray → Option (State × Memory.Mem × Nat))
    (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c)
    (hN : invokeNativeNone s sc)
    (h0 : (Runner.cpiCallNextState registry s sc fuel' runCallee).regs.r0 = 0) :
    ∃ elf sf m f, registry (invokePid s sc) = some elf ∧ runCallee elf = some (sf, m, f) ∧
      sf.exitCode.getD 1 = 0 ∧
      (Runner.cpiCallNextState registry s sc fuel' runCallee).mem = m := by
  revert h0
  rcases hsc with rfl | rfl <;>
    (unfold Runner.cpiCallNextState
     extract_lets
     repeat' split
     all_goals intro h0
     all_goals first
       | (simp at h0; done)
       | (rename_i hnat
          have hN' := hN
          unfold invokeNativeNone at hN'
          exact absurd (hnat.symm.trans hN') (Option.some_ne_none _))
       | (simp only [applyResult_r0] at h0
          exact ⟨_, _, _, _, by assumption, by assumption, h0, by simp [applyResult, h0]⟩))


/-- `stepCpi` form of `cpiCallNextState_success` for the C ABI: the callee
    build, its run and the commit that produced code 0. -/
theorem stepCpi_c_success (registry : Nat → Option ByteArray)
    (subRun : (Nat → Option Insn) → State → Nat → State × Nat) (s : State) (fuel' : Nat)
    (hN : invokeNativeNone s .sol_invoke_signed_c)
    (h0 : (Runner.stepCpi registry subRun s fuel' (.call .sol_invoke_signed_c)).regs.r0 = 0) :
    ∃ elf insns subS slots,
      registry (invokePid s .sol_invoke_signed_c) = some elf ∧
      Runner.buildCalleeVM s fuel'
          (Runner.readMemBytes s.mem (Memory.readU64 s.mem s.regs.r1) 32)
          (invokeAccts s .sol_invoke_signed_c) (invokeIxData s .sol_invoke_signed_c) elf
        = some (insns, subS, slots) ∧
      (Runner.commitCallee s.mem slots (subRun (Runner.fetchFromArray insns) subS fuel').1
          (subRun (Runner.fetchFromArray insns) subS fuel').2).1.exitCode.getD 1 = 0 ∧
      (Runner.stepCpi registry subRun s fuel' (.call .sol_invoke_signed_c)).mem =
        (Runner.commitCallee s.mem slots (subRun (Runner.fetchFromArray insns) subS fuel').1
          (subRun (Runner.fetchFromArray insns) subS fuel').2).2.1 := by
  revert h0
  unfold Runner.stepCpi
  extract_lets runCallee
  intro h0
  obtain ⟨elf, sf, m, f, hreg, hrun, hc, hm⟩ :=
    cpiCallNextState_success registry s _ fuel' _ (by simp) hN h0
  simp only [runCallee, bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨⟨insns, subS, slots⟩, hbuild, hrun⟩ := hrun
  simp only [Option.some.injEq] at hrun
  refine ⟨elf, insns, subS, slots, hreg, hbuild, ?_, ?_⟩
  · rw [hrun]; exact hc
  · rw [hm, hrun]

end Cpi
end SVM.SBPF
