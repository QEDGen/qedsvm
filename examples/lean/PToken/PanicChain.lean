/-
  p_token's 12 panic sites abort. Each site in the entrypoint calls a noreturn helper
  (11177 or 10881) whose code is straight-line frame setup followed by a call down a chain
  that ends in `sol_panic_`:

    11177  call_local 11618
    11618..11639 (setup)  11640 call_local 10862      10881..10902 (setup)  10903 call_local 10862
    10862..10866 (setup)  10867 call_local 10823
    10823..10828 (load the panic location)  10829 call sol_panic_

  No step of the chain is control flow, so each either faults or falls through
  (`failsClosed_straight`), each call pushes or faults on the depth limit
  (`failsClosed_enter`), and `sol_panic_` sets a typed fault. Nothing about the data the
  chain moves is needed. Pins tie `PanicCode` to the real `.text` (`PanicChainPins`).
-/
import SVM.SBPF.FailClosed

namespace Examples.PTokenPanicChain

open SVM.SBPF

/-- The entrypoint's call sites into the noreturn panic helpers (`qed_analysis::cfg`). -/
def panicSites : List Nat := [6428, 6441, 6445, 6543, 6547, 6635, 6639, 6652, 6656, 6660, 6803, 6863]

/-- The panic chain's instructions, as `fetch` must serve them. -/
structure PanicCode (fetch : Nat → Option Insn) : Prop where
  c11177 : fetch 11177 = some (.call_local 11618)
  r11618 : StraightRun fetch 11618 22
  c11640 : fetch 11640 = some (.call_local 10862)
  r10881 : StraightRun fetch 10881 22
  c10903 : fetch 10903 = some (.call_local 10862)
  r10862 : StraightRun fetch 10862 5
  c10867 : fetch 10867 = some (.call_local 10823)
  r10823 : StraightRun fetch 10823 6
  p10829 : fetch 10829 = some (.call .sol_panic_)
  sites : ∀ site ∈ panicSites,
    fetch site = some (.call_local 11177) ∨ fetch site = some (.call_local 10881)

theorem panic10823 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (s : State)
    (hpc : s.pc = 10823) (h0 : s.exitCode = none) : FailsClosed fetch s :=
  failsClosed_straight fetch 6 s h0 (by rw [hpc]; exact hc.r10823) fun u hu h0u _ =>
    failsClosed_panic fetch u h0u (by rw [hu, hpc]; exact hc.p10829)

theorem panic10862 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (s : State)
    (hpc : s.pc = 10862) (h0 : s.exitCode = none) : FailsClosed fetch s :=
  failsClosed_straight fetch 5 s h0 (by rw [hpc]; exact hc.r10862) fun u hu h0u _ =>
    failsClosed_enter fetch u 10823 h0u (by rw [hu, hpc]; exact hc.c10867) fun v hv h0v =>
      panic10823 fetch hc v hv h0v

theorem panic11177 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (s : State)
    (hpc : s.pc = 11177) (h0 : s.exitCode = none) : FailsClosed fetch s :=
  failsClosed_enter fetch s 11618 h0 (by rw [hpc]; exact hc.c11177) fun u hu h0u =>
    failsClosed_straight fetch 22 u h0u (by rw [hu]; exact hc.r11618) fun v hv h0v _ =>
      failsClosed_enter fetch v 10862 h0v (by rw [hv, hu]; exact hc.c11640) fun w hw h0w =>
        panic10862 fetch hc w hw h0w

theorem panic10881 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (s : State)
    (hpc : s.pc = 10881) (h0 : s.exitCode = none) : FailsClosed fetch s :=
  failsClosed_straight fetch 22 s h0 (by rw [hpc]; exact hc.r10881) fun u hu h0u _ =>
    failsClosed_enter fetch u 10862 h0u (by rw [hu, hpc]; exact hc.c10903) fun v hv h0v =>
      panic10862 fetch hc v hv h0v

/-- **Every panic site aborts.** From any of the entrypoint's 12 panic sites, with any call
    stack, no run halts with exit code 0 unless it carries a typed fault. -/
theorem panic_sites_fail_closed (fetch : Nat → Option Insn) (hc : PanicCode fetch)
    (site : Nat) (hsite : site ∈ panicSites) (s : State) (hpc : s.pc = site)
    (h0 : s.exitCode = none) : FailsClosed fetch s := by
  rcases hc.sites site hsite with h | h
  · exact failsClosed_enter fetch s 11177 h0 (by rw [hpc]; exact h) fun u hu h0u =>
      panic11177 fetch hc u hu h0u
  · exact failsClosed_enter fetch s 10881 h0 (by rw [hpc]; exact h) fun u hu h0u =>
      panic10881 fetch hc u hu h0u

/-! ## The panic helpers never return -/

theorem stays10823 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (base : List CallFrame)
    (s : State) (hpc : s.pc = 10823) (h0 : s.exitCode = none)
    (hcs : ∃ ys, s.callStack = ys ++ base) : StaysAbove fetch base s :=
  staysAbove_straight fetch base 6 s h0 hcs (by rw [hpc]; exact hc.r10823) fun u hu h0u hcsu =>
    staysAbove_panic fetch base u h0u (by rw [hcsu]; exact hcs)
      (by rw [hu, hpc]; exact hc.p10829)

theorem stays10862 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (base : List CallFrame)
    (s : State) (hpc : s.pc = 10862) (h0 : s.exitCode = none)
    (hcs : ∃ ys, s.callStack = ys ++ base) : StaysAbove fetch base s :=
  staysAbove_straight fetch base 5 s h0 hcs (by rw [hpc]; exact hc.r10862) fun u hu h0u hcsu =>
    staysAbove_enter fetch base u 10823 h0u (by rw [hcsu]; exact hcs)
      (by rw [hu, hpc]; exact hc.c10867) fun v hv h0v hcsv =>
        stays10823 fetch hc base v hv h0v hcsv

theorem stays11177 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (base : List CallFrame)
    (s : State) (hpc : s.pc = 11177) (h0 : s.exitCode = none)
    (hcs : ∃ ys, s.callStack = ys ++ base) : StaysAbove fetch base s :=
  staysAbove_enter fetch base s 11618 h0 hcs (by rw [hpc]; exact hc.c11177) fun u hu h0u hcsu =>
    staysAbove_straight fetch base 22 u h0u hcsu (by rw [hu]; exact hc.r11618)
      fun v hv h0v hcsv =>
        staysAbove_enter fetch base v 10862 h0v (by rw [hcsv]; exact hcsu)
          (by rw [hv, hu]; exact hc.c11640) fun w hw h0w hcsw =>
            stays10862 fetch hc base w hw h0w hcsw

theorem stays10881 (fetch : Nat → Option Insn) (hc : PanicCode fetch) (base : List CallFrame)
    (s : State) (hpc : s.pc = 10881) (h0 : s.exitCode = none)
    (hcs : ∃ ys, s.callStack = ys ++ base) : StaysAbove fetch base s :=
  staysAbove_straight fetch base 22 s h0 hcs (by rw [hpc]; exact hc.r10881) fun u hu h0u hcsu =>
    staysAbove_enter fetch base u 10862 h0u (by rw [hcsu]; exact hcs)
      (by rw [hu, hpc]; exact hc.c10903) fun v hv h0v hcsv =>
        stays10862 fetch hc base v hv h0v hcsv

/-- The entrypoint's two panic helpers never return to their caller. -/
theorem panic_helpers_noReturn (fetch : Nat → Option Insn) (hc : PanicCode fetch) (t : Nat)
    (ht : (t == 11177 || t == 10881) = true) : NoReturn fetch t := by
  intro s F0 outer hpc hcs h0
  have hbase : ∃ ys, s.callStack = ys ++ F0 :: outer := ⟨[], by simp [hcs]⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with ht | ht <;> subst ht
  · exact stays11177 fetch hc _ s hpc h0 hbase
  · exact stays10881 fetch hc _ s hpc h0 hbase

end Examples.PTokenPanicChain
