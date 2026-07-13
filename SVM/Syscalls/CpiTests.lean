import SVM.Syscalls.Cpi

namespace SVM.SBPF.Cpi.Tests

private def callerMem : Memory.Mem :=
  { default := fun addr => if addr = 7 then 3 else 0 }

private def nestedMem : Memory.Mem :=
  { default := fun addr => if addr = 7 then 11 else 0 }

private def caller : State :=
  { (default : State) with mem := callerMem, pc := 5, cuConsumed := 10 }

private def innerSuccess : CalleeResult :=
  { code := 0
    mem := nestedMem
    log := #[⟨#[0x11]⟩]
    returnData := ⟨#[0xaa]⟩
    returnDataProgId := ⟨Array.replicate 32 1⟩
    cuConsumed := 20 }

/-- The enclosing callee exposes the account state produced by its successful
    nested CPI and replaces the transaction-wide return-data channel. -/
private def outerSuccess : CalleeResult :=
  { code := 0
    mem := (applyResult (default : State) innerSuccess).mem
    log := #[⟨#[0x11]⟩, ⟨#[0x22]⟩]
    returnData := ⟨#[0xbb, 0xcc]⟩
    returnDataProgId := ⟨Array.replicate 32 2⟩
    cuConsumed := 33 }

/-- An enclosing program error proposes the same nested account state, but the
    transaction boundary must discard it wholesale. -/
private def outerFailure : CalleeResult :=
  { outerSuccess with code := 7, returnData := ⟨#[0xee]⟩ }

private def verifiedOuter : CalleeSemantics :=
  fun _ result => result = outerSuccess

example : Transitions verifiedOuter caller (applyResult caller outerSuccess) := by
  exact ⟨outerSuccess, rfl, rfl⟩

example : (applyResult caller outerSuccess).mem 7 = 11 := by
  simp [applyResult, outerSuccess, innerSuccess, nestedMem, Memory.Mem.read]

example : (applyResult caller outerSuccess).returnData = ⟨#[0xbb, 0xcc]⟩ := by
  rfl

example : (applyResult caller outerSuccess).cuConsumed = 10 + cu + 33 := by
  rfl

example : (applyResult caller outerFailure).mem 7 = 3 := by
  simp [applyResult, outerFailure, outerSuccess, caller, callerMem, Memory.Mem.read]

example : (applyResult caller outerFailure).regs.r0 = 7 := by
  rfl

/-- Return data is transaction-scoped and remains observable even though the
    failed invocation's account mutations are rolled back. -/
example : (applyResult caller outerFailure).returnData = ⟨#[0xee]⟩ := by
  rfl

end SVM.SBPF.Cpi.Tests
