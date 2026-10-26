/-
  Input conditions for p_token's six loop-free success edges (GENERATED; regenerate rather
  than edit). `SuccessPaths` proves which guards a run reaching each edge passed; here the
  checked abstract interpretation (`AbsInterp`, from the entrypoint with `r1` the input
  pointer, `r10` the frame pointer and no input written yet) pins most guards' operands to
  fixed input fields or constants, so each pinned guard becomes a fact about the input bytes
  the run started from (`IGuard.holds`).

  Unpinned guards, which compare values read through pointers that depend on account data
  lengths (the instruction data, so the amount and the instruction length), stay as
  register facts in `SuccessPaths`.
-/
import PToken.SuccessPaths
import SVM.SBPF.InputGuards

namespace Examples.PTokenSuccessPaths

open SVM.SBPF Examples.PTokenErrorTail

/-- The entrypoint's initial abstract state: `r1` points at the input, `r10` is the frame
    pointer, no input has been written. -/
def ptInit : AState := { r1 := .inPtr 0, r10 := .fp, written := some [] }

theorem ptInit_concrete (s0 : State) (h1 : s0.regs.r1 = Memory.INPUT_START)
    (h10 : s0.regs.r10 = STACK_TOP) : Concrete s0 ptInit s0 := by
  refine ⟨fun r => ?_, fun _ _ _ _ _ => rfl⟩
  cases r
  case r1 => show s0.regs.r1 = Memory.INPUT_START + 0; rw [h1]; rfl
  case r10 => exact h10
  all_goals trivial

/-- The abstract map of p_token's entrypoint. -/
def ptAbsMap (insns : Array Insn) : Array (Option AState) :=
  absMap (Runner.fetchFromArray insns) ptNoret insns.size 198 ptInit

theorem absOk : ptokenInsns.all (fun insns =>
    absCheck (Runner.fetchFromArray insns) ptNoret (ptAbsMap insns) 198 ptInit) = true := by
  native_decide

/-! ### Edge 4825: Transfer, amount moved -/

def idom4825 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩  -- jne r0, r5, 4724
]

def ipre4825_4816 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 }, (.inLoad .dword 128), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 }, (.inLoad .dword 136), (.inLoad .dword 21032)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 }, (.inLoad .dword 144), (.inLoad .dword 21040)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }, (.inLoad .dword 152), (.inLoad .dword 21048)⟩  -- jne r0, r5, 4725
]

def ipost4825_4816 : List IGuard := [
  ⟨{ pc := 4816, insn := .jeq .r4 (.imm 0) 5716, onSucc := 4817 }, (.inLoad .byte 21017), (.const 0)⟩  -- jeq r4, 0, 5716
]

def ipre4825_5216 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r0, 1, 4457
  ⟨{ pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 }, (.inLoad .dword 172), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4457
  ⟨{ pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 }, (.inLoad .dword 180), (.inLoad .dword 21032)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 }, (.inLoad .dword 188), (.inLoad .dword 21040)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }, (.inLoad .dword 196), (.inLoad .dword 21048)⟩  -- jne r8, r0, 4457
]

def ipost4825_5216 : List IGuard := [
  ⟨{ pc := 5216, insn := .jeq .r4 (.imm 0) 5716, onSucc := 5217 }, (.inLoad .byte 21017), (.const 0)⟩  -- jeq r4, 0, 5716
]

def ipre4825_5715 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 }, (.inLoad .dword 128), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 }, (.inLoad .dword 136), (.inLoad .dword 21032)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 }, (.inLoad .dword 144), (.inLoad .dword 21040)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }, (.inLoad .dword 152), (.inLoad .dword 21048)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4469, insn := .jne .r4 (.imm 355) 4815, onSucc := 4470 }, (.inLoad .dword 21096), (.const 355)⟩,  -- jne r4, 355, 4815
  ⟨{ pc := 5713, insn := .jne .r4 (.imm 1) 6235, onSucc := 5714 }, (.inLoad .byte 21106), (.const 1)⟩  -- jne r4, 1, 6235
]

def ipost4825_5715 : List IGuard := [
  ⟨{ pc := 5715, insn := .jeq .r4 (.imm 0) 4817, onSucc := 4817 }, (.inLoad .byte 21104), (.const 0)⟩  -- jeq r4, 0, 4817
]

def ipre4825_6233 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r0, 1, 4457
  ⟨{ pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 }, (.inLoad .dword 172), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4457
  ⟨{ pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 }, (.inLoad .dword 180), (.inLoad .dword 21032)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 }, (.inLoad .dword 188), (.inLoad .dword 21040)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }, (.inLoad .dword 196), (.inLoad .dword 21048)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4043, insn := .jne .r4 (.imm 355) 5215, onSucc := 4044 }, (.inLoad .dword 21096), (.const 355)⟩,  -- jne r4, 355, 5215
  ⟨{ pc := 6231, insn := .jne .r4 (.imm 1) 6235, onSucc := 6232 }, (.inLoad .byte 21106), (.const 1)⟩  -- jne r4, 1, 6235
]

def ipost4825_6233 : List IGuard := [
  ⟨{ pc := 6233, insn := .jeq .r4 (.imm 0) 5217, onSucc := 5217 }, (.inLoad .byte 21104), (.const 0)⟩  -- jeq r4, 0, 5217
]

def iroutes4825 : List IRoute :=
  [(4816, ipre4825_4816, ipost4825_4816), (5216, ipre4825_5216, ipost4825_5216), (5715, ipre4825_5715, ipost4825_5715), (6233, ipre4825_6233, ipost4825_6233)]

theorem pins4825 : ptokenInsns.all (fun insns =>
    let m := ptAbsMap insns
    (idom4825.all (iguardCheck m) &&
      iroutes4825.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) &&
    iguardsMatch dom4825 routes4825 idom4825 iroutes4825) = true := by native_decide

/-- **Input conditions for edge 4825** (Transfer, amount moved). A run of p_token's decoded `.text` from
    the entrypoint, on an input described by `ptInit`, that stands at the edge started from an
    input satisfying its pinned dominating guards and one authority route's pinned guards. -/
theorem inputs4825 (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (hinit : Concrete s0 ptInit s0) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 4825) :
    (∀ ig ∈ idom4825, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes4825 ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  have hpath := check4825
  rw [hp, Option.all_some] at hpath
  have habs := absOk
  rw [hp, Option.all_some] at habs
  have hpins := pins4825
  rw [hp, Option.all_some] at hpins
  simp only [Bool.and_eq_true] at hpins
  exact edge_input_conditions _ ptNoret (ptNoret_sound insns hp) _ 198 4825 _ _ _ _ _ _ hpath
    habs (by simpa only [Bool.and_eq_true] using hpins.1) hpins.2 s0 hpc hcs hinit n hend

/-! ### Edge 4832: Transfer, native SOL -/

def idom4832 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 }, (.inLoad .byte 205), (.const 1)⟩  -- jne r3, 1, 3542
]

def ipre4832_4816 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 }, (.inLoad .dword 128), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 }, (.inLoad .dword 136), (.inLoad .dword 21032)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 }, (.inLoad .dword 144), (.inLoad .dword 21040)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }, (.inLoad .dword 152), (.inLoad .dword 21048)⟩  -- jne r0, r5, 4725
]

def ipost4832_4816 : List IGuard := [
  ⟨{ pc := 4816, insn := .jeq .r4 (.imm 0) 5716, onSucc := 4817 }, (.inLoad .byte 21017), (.const 0)⟩,  -- jeq r4, 0, 5716
  ⟨{ pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 }, (.inLoad .byte 205), (.const 1)⟩  -- jne r3, 1, 3542
]

def ipre4832_5216 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r0, 1, 4457
  ⟨{ pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 }, (.inLoad .dword 172), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4457
  ⟨{ pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 }, (.inLoad .dword 180), (.inLoad .dword 21032)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 }, (.inLoad .dword 188), (.inLoad .dword 21040)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }, (.inLoad .dword 196), (.inLoad .dword 21048)⟩  -- jne r8, r0, 4457
]

def ipost4832_5216 : List IGuard := [
  ⟨{ pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 }, (.inLoad .byte 205), (.const 1)⟩,  -- jne r3, 1, 3542
  ⟨{ pc := 5216, insn := .jeq .r4 (.imm 0) 5716, onSucc := 5217 }, (.inLoad .byte 21017), (.const 0)⟩  -- jeq r4, 0, 5716
]

def ipre4832_5715 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 }, (.inLoad .dword 128), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 }, (.inLoad .dword 136), (.inLoad .dword 21032)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 }, (.inLoad .dword 144), (.inLoad .dword 21040)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }, (.inLoad .dword 152), (.inLoad .dword 21048)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4469, insn := .jne .r4 (.imm 355) 4815, onSucc := 4470 }, (.inLoad .dword 21096), (.const 355)⟩,  -- jne r4, 355, 4815
  ⟨{ pc := 5713, insn := .jne .r4 (.imm 1) 6235, onSucc := 5714 }, (.inLoad .byte 21106), (.const 1)⟩  -- jne r4, 1, 6235
]

def ipost4832_5715 : List IGuard := [
  ⟨{ pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 }, (.inLoad .byte 205), (.const 1)⟩,  -- jne r3, 1, 3542
  ⟨{ pc := 5715, insn := .jeq .r4 (.imm 0) 4817, onSucc := 4817 }, (.inLoad .byte 21104), (.const 0)⟩  -- jeq r4, 0, 4817
]

def ipre4832_6233 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r0, 1, 4457
  ⟨{ pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 }, (.inLoad .dword 172), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4457
  ⟨{ pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 }, (.inLoad .dword 180), (.inLoad .dword 21032)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 }, (.inLoad .dword 188), (.inLoad .dword 21040)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }, (.inLoad .dword 196), (.inLoad .dword 21048)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4043, insn := .jne .r4 (.imm 355) 5215, onSucc := 4044 }, (.inLoad .dword 21096), (.const 355)⟩,  -- jne r4, 355, 5215
  ⟨{ pc := 6231, insn := .jne .r4 (.imm 1) 6235, onSucc := 6232 }, (.inLoad .byte 21106), (.const 1)⟩  -- jne r4, 1, 6235
]

def ipost4832_6233 : List IGuard := [
  ⟨{ pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 }, (.inLoad .byte 205), (.const 1)⟩,  -- jne r3, 1, 3542
  ⟨{ pc := 6233, insn := .jeq .r4 (.imm 0) 5217, onSucc := 5217 }, (.inLoad .byte 21104), (.const 0)⟩  -- jeq r4, 0, 5217
]

def iroutes4832 : List IRoute :=
  [(4816, ipre4832_4816, ipost4832_4816), (5216, ipre4832_5216, ipost4832_5216), (5715, ipre4832_5715, ipost4832_5715), (6233, ipre4832_6233, ipost4832_6233)]

theorem pins4832 : ptokenInsns.all (fun insns =>
    let m := ptAbsMap insns
    (idom4832.all (iguardCheck m) &&
      iroutes4832.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) &&
    iguardsMatch dom4832 routes4832 idom4832 iroutes4832) = true := by native_decide

/-- **Input conditions for edge 4832** (Transfer, native SOL). A run of p_token's decoded `.text` from
    the entrypoint, on an input described by `ptInit`, that stands at the edge started from an
    input satisfying its pinned dominating guards and one authority route's pinned guards. -/
theorem inputs4832 (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (hinit : Concrete s0 ptInit s0) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 4832) :
    (∀ ig ∈ idom4832, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes4832 ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  have hpath := check4832
  rw [hp, Option.all_some] at hpath
  have habs := absOk
  rw [hp, Option.all_some] at habs
  have hpins := pins4832
  rw [hp, Option.all_some] at hpins
  simp only [Bool.and_eq_true] at hpins
  exact edge_input_conditions _ ptNoret (ptNoret_sound insns hp) _ 198 4832 _ _ _ _ _ _ hpath
    habs (by simpa only [Bool.and_eq_true] using hpins.1) hpins.2 s0 hpc hcs hinit n hend

/-! ### Edge 5250: Transfer of 0 -/

def idom5250 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 }, (.inLoad .dword 10552), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 }, (.inLoad .dword 10560), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }, (.inLoad .dword 10568), (.const 10463932726783620124)⟩  -- jne r2, r3, 5717
]

def ipre5250_4816 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 }, (.inLoad .dword 128), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 }, (.inLoad .dword 136), (.inLoad .dword 21032)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 }, (.inLoad .dword 144), (.inLoad .dword 21040)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }, (.inLoad .dword 152), (.inLoad .dword 21048)⟩  -- jne r0, r5, 4725
]

def ipost5250_4816 : List IGuard := [
  ⟨{ pc := 4816, insn := .jeq .r4 (.imm 0) 5716, onSucc := 4817 }, (.inLoad .byte 21017), (.const 0)⟩,  -- jeq r4, 0, 5716
  ⟨{ pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 }, (.inLoad .dword 10552), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 }, (.inLoad .dword 10560), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }, (.inLoad .dword 10568), (.const 10463932726783620124)⟩  -- jne r2, r3, 5717
]

def ipre5250_5216 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r0, 1, 4457
  ⟨{ pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 }, (.inLoad .dword 172), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4457
  ⟨{ pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 }, (.inLoad .dword 180), (.inLoad .dword 21032)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 }, (.inLoad .dword 188), (.inLoad .dword 21040)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }, (.inLoad .dword 196), (.inLoad .dword 21048)⟩  -- jne r8, r0, 4457
]

def ipost5250_5216 : List IGuard := [
  ⟨{ pc := 5216, insn := .jeq .r4 (.imm 0) 5716, onSucc := 5217 }, (.inLoad .byte 21017), (.const 0)⟩,  -- jeq r4, 0, 5716
  ⟨{ pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 }, (.inLoad .dword 10552), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 }, (.inLoad .dword 10560), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }, (.inLoad .dword 10568), (.const 10463932726783620124)⟩  -- jne r2, r3, 5717
]

def ipre5250_5715 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 }, (.inLoad .dword 128), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 }, (.inLoad .dword 136), (.inLoad .dword 21032)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 }, (.inLoad .dword 144), (.inLoad .dword 21040)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }, (.inLoad .dword 152), (.inLoad .dword 21048)⟩,  -- jne r0, r5, 4725
  ⟨{ pc := 4469, insn := .jne .r4 (.imm 355) 4815, onSucc := 4470 }, (.inLoad .dword 21096), (.const 355)⟩,  -- jne r4, 355, 4815
  ⟨{ pc := 5713, insn := .jne .r4 (.imm 1) 6235, onSucc := 5714 }, (.inLoad .byte 21106), (.const 1)⟩  -- jne r4, 1, 6235
]

def ipost5250_5715 : List IGuard := [
  ⟨{ pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 }, (.inLoad .dword 10552), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 }, (.inLoad .dword 10560), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }, (.inLoad .dword 10568), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5715, insn := .jeq .r4 (.imm 0) 4817, onSucc := 4817 }, (.inLoad .byte 21104), (.const 0)⟩  -- jeq r4, 0, 4817
]

def ipre5250_6233 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 }, (.inLoad .dword 10592), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 }, (.inLoad .byte 21016), (.const 255)⟩,  -- jeq r2, 255, 3991
  ⟨{ pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jgt r5, 2, 4725
  ⟨{ pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 }, (.inLoad .byte 10708), (.const 0)⟩,  -- jeq r5, 0, 5080
  ⟨{ pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 }, (.inLoad .byte 10708), (.const 2)⟩,  -- jeq r5, 2, 4725
  ⟨{ pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 }, (.inLoad .dword 96), (.inLoad .dword 10600)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 }, (.inLoad .dword 104), (.inLoad .dword 10608)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 }, (.inLoad .dword 112), (.inLoad .dword 10616)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }, (.inLoad .dword 120), (.inLoad .dword 10624)⟩,  -- jne r0, r5, 4724
  ⟨{ pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r0, 1, 4457
  ⟨{ pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 }, (.inLoad .dword 172), (.inLoad .dword 21024)⟩,  -- jne r0, r5, 4457
  ⟨{ pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 }, (.inLoad .dword 180), (.inLoad .dword 21032)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 }, (.inLoad .dword 188), (.inLoad .dword 21040)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }, (.inLoad .dword 196), (.inLoad .dword 21048)⟩,  -- jne r8, r0, 4457
  ⟨{ pc := 4043, insn := .jne .r4 (.imm 355) 5215, onSucc := 4044 }, (.inLoad .dword 21096), (.const 355)⟩,  -- jne r4, 355, 5215
  ⟨{ pc := 6231, insn := .jne .r4 (.imm 1) 6235, onSucc := 6232 }, (.inLoad .byte 21106), (.const 1)⟩  -- jne r4, 1, 6235
]

def ipost5250_6233 : List IGuard := [
  ⟨{ pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 }, (.inLoad .dword 10552), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 }, (.inLoad .dword 10560), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }, (.inLoad .dword 10568), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 6233, insn := .jeq .r4 (.imm 0) 5217, onSucc := 5217 }, (.inLoad .byte 21104), (.const 0)⟩  -- jeq r4, 0, 5217
]

def iroutes5250 : List IRoute :=
  [(4816, ipre5250_4816, ipost5250_4816), (5216, ipre5250_5216, ipost5250_5216), (5715, ipre5250_5715, ipost5250_5715), (6233, ipre5250_6233, ipost5250_6233)]

theorem pins5250 : ptokenInsns.all (fun insns =>
    let m := ptAbsMap insns
    (idom5250.all (iguardCheck m) &&
      iroutes5250.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) &&
    iguardsMatch dom5250 routes5250 idom5250 iroutes5250) = true := by native_decide

/-- **Input conditions for edge 5250** (Transfer of 0). A run of p_token's decoded `.text` from
    the entrypoint, on an input described by `ptInit`, that stands at the edge started from an
    input satisfying its pinned dominating guards and one authority route's pinned guards. -/
theorem inputs5250 (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (hinit : Concrete s0 ptInit s0) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 5250) :
    (∀ ig ∈ idom5250, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes5250 ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  have hpath := check5250
  rw [hp, Option.all_some] at hpath
  have habs := absOk
  rw [hp, Option.all_some] at habs
  have hpins := pins5250
  rw [hp, Option.all_some] at hpins
  simp only [Bool.and_eq_true] at hpins
  exact edge_input_conditions _ ptNoret (ptNoret_sound insns hp) _ 198 5250 _ _ _ _ _ _ hpath
    habs (by simpa only [Bool.and_eq_true] using hpins.1) hpins.2 s0 hpc hcs hinit n hend

/-! ### Edge 5063: TransferChecked, amount moved -/

def idom5063 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩  -- jne r0, 1, 5078
]

def ipre5063_5053 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 }, (.inLoad .dword 128), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4725
  ⟨{ pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 }, (.inLoad .dword 136), (.inLoad .dword 31456)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 }, (.inLoad .dword 144), (.inLoad .dword 31464)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }, (.inLoad .dword 152), (.inLoad .dword 31472)⟩  -- jne r5, r3, 4725
]

def ipost5063_5053 : List IGuard := [
  ⟨{ pc := 5053, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5054 }, (.inLoad .byte 31441), (.const 0)⟩  -- jeq r3, 0, 5716
]

def ipre5063_5438 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r3, 1, 4839
  ⟨{ pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 }, (.inLoad .dword 172), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4839
  ⟨{ pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 }, (.inLoad .dword 180), (.inLoad .dword 31456)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 }, (.inLoad .dword 188), (.inLoad .dword 31464)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }, (.inLoad .dword 196), (.inLoad .dword 31472)⟩  -- jne r0, r3, 4839
]

def ipost5063_5438 : List IGuard := [
  ⟨{ pc := 5438, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5439 }, (.inLoad .byte 31441), (.const 0)⟩  -- jeq r3, 0, 5716
]

def ipre5063_5995 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 }, (.inLoad .dword 128), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4725
  ⟨{ pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 }, (.inLoad .dword 136), (.inLoad .dword 31456)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 }, (.inLoad .dword 144), (.inLoad .dword 31464)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }, (.inLoad .dword 152), (.inLoad .dword 31472)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4851, insn := .jne .r4 (.imm 355) 5052, onSucc := 4852 }, (.inLoad .dword 31520), (.const 355)⟩,  -- jne r4, 355, 5052
  ⟨{ pc := 5993, insn := .jne .r4 (.imm 1) 6434, onSucc := 5994 }, (.inLoad .byte 31530), (.const 1)⟩  -- jne r4, 1, 6434
]

def ipost5063_5995 : List IGuard := [
  ⟨{ pc := 5995, insn := .jeq .r3 (.imm 0) 5054, onSucc := 5054 }, (.inLoad .byte 31528), (.const 0)⟩  -- jeq r3, 0, 5054
]

def ipre5063_6432 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r3, 1, 4839
  ⟨{ pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 }, (.inLoad .dword 172), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4839
  ⟨{ pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 }, (.inLoad .dword 180), (.inLoad .dword 31456)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 }, (.inLoad .dword 188), (.inLoad .dword 31464)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }, (.inLoad .dword 196), (.inLoad .dword 31472)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 288, insn := .jne .r4 (.imm 355) 5437, onSucc := 289 }, (.inLoad .dword 31520), (.const 355)⟩,  -- jne r4, 355, 5437
  ⟨{ pc := 6430, insn := .jne .r4 (.imm 1) 6434, onSucc := 6431 }, (.inLoad .byte 31530), (.const 1)⟩  -- jne r4, 1, 6434
]

def ipost5063_6432 : List IGuard := [
  ⟨{ pc := 6432, insn := .jeq .r3 (.imm 0) 5439, onSucc := 5439 }, (.inLoad .byte 31528), (.const 0)⟩  -- jeq r3, 0, 5439
]

def iroutes5063 : List IRoute :=
  [(5053, ipre5063_5053, ipost5063_5053), (5438, ipre5063_5438, ipost5063_5438), (5995, ipre5063_5995, ipost5063_5995), (6432, ipre5063_6432, ipost5063_6432)]

theorem pins5063 : ptokenInsns.all (fun insns =>
    let m := ptAbsMap insns
    (idom5063.all (iguardCheck m) &&
      iroutes5063.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) &&
    iguardsMatch dom5063 routes5063 idom5063 iroutes5063) = true := by native_decide

/-- **Input conditions for edge 5063** (TransferChecked, amount moved). A run of p_token's decoded `.text` from
    the entrypoint, on an input described by `ptInit`, that stands at the edge started from an
    input satisfying its pinned dominating guards and one authority route's pinned guards. -/
theorem inputs5063 (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (hinit : Concrete s0 ptInit s0) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 5063) :
    (∀ ig ∈ idom5063, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes5063 ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  have hpath := check5063
  rw [hp, Option.all_some] at hpath
  have habs := absOk
  rw [hp, Option.all_some] at habs
  have hpins := pins5063
  rw [hp, Option.all_some] at hpins
  simp only [Bool.and_eq_true] at hpins
  exact edge_input_conditions _ ptNoret (ptNoret_sound insns hp) _ 198 5063 _ _ _ _ _ _ hpath
    habs (by simpa only [Bool.and_eq_true] using hpins.1) hpins.2 s0 hpc hcs hinit n hend

/-! ### Edge 5070: TransferChecked, native SOL -/

def idom5070 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 }, (.inLoad .byte 205), (.const 1)⟩  -- jne r3, 1, 3542
]

def ipre5070_5053 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 }, (.inLoad .dword 128), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4725
  ⟨{ pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 }, (.inLoad .dword 136), (.inLoad .dword 31456)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 }, (.inLoad .dword 144), (.inLoad .dword 31464)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }, (.inLoad .dword 152), (.inLoad .dword 31472)⟩  -- jne r5, r3, 4725
]

def ipost5070_5053 : List IGuard := [
  ⟨{ pc := 5053, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5054 }, (.inLoad .byte 31441), (.const 0)⟩,  -- jeq r3, 0, 5716
  ⟨{ pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 }, (.inLoad .byte 205), (.const 1)⟩  -- jne r3, 1, 3542
]

def ipre5070_5438 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r3, 1, 4839
  ⟨{ pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 }, (.inLoad .dword 172), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4839
  ⟨{ pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 }, (.inLoad .dword 180), (.inLoad .dword 31456)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 }, (.inLoad .dword 188), (.inLoad .dword 31464)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }, (.inLoad .dword 196), (.inLoad .dword 31472)⟩  -- jne r0, r3, 4839
]

def ipost5070_5438 : List IGuard := [
  ⟨{ pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 }, (.inLoad .byte 205), (.const 1)⟩,  -- jne r3, 1, 3542
  ⟨{ pc := 5438, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5439 }, (.inLoad .byte 31441), (.const 0)⟩  -- jeq r3, 0, 5716
]

def ipre5070_5995 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 }, (.inLoad .dword 128), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4725
  ⟨{ pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 }, (.inLoad .dword 136), (.inLoad .dword 31456)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 }, (.inLoad .dword 144), (.inLoad .dword 31464)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }, (.inLoad .dword 152), (.inLoad .dword 31472)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4851, insn := .jne .r4 (.imm 355) 5052, onSucc := 4852 }, (.inLoad .dword 31520), (.const 355)⟩,  -- jne r4, 355, 5052
  ⟨{ pc := 5993, insn := .jne .r4 (.imm 1) 6434, onSucc := 5994 }, (.inLoad .byte 31530), (.const 1)⟩  -- jne r4, 1, 6434
]

def ipost5070_5995 : List IGuard := [
  ⟨{ pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 }, (.inLoad .byte 205), (.const 1)⟩,  -- jne r3, 1, 3542
  ⟨{ pc := 5995, insn := .jeq .r3 (.imm 0) 5054, onSucc := 5054 }, (.inLoad .byte 31528), (.const 0)⟩  -- jeq r3, 0, 5054
]

def ipre5070_6432 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r3, 1, 4839
  ⟨{ pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 }, (.inLoad .dword 172), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4839
  ⟨{ pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 }, (.inLoad .dword 180), (.inLoad .dword 31456)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 }, (.inLoad .dword 188), (.inLoad .dword 31464)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }, (.inLoad .dword 196), (.inLoad .dword 31472)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 288, insn := .jne .r4 (.imm 355) 5437, onSucc := 289 }, (.inLoad .dword 31520), (.const 355)⟩,  -- jne r4, 355, 5437
  ⟨{ pc := 6430, insn := .jne .r4 (.imm 1) 6434, onSucc := 6431 }, (.inLoad .byte 31530), (.const 1)⟩  -- jne r4, 1, 6434
]

def ipost5070_6432 : List IGuard := [
  ⟨{ pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 }, (.inLoad .byte 205), (.const 1)⟩,  -- jne r3, 1, 3542
  ⟨{ pc := 6432, insn := .jeq .r3 (.imm 0) 5439, onSucc := 5439 }, (.inLoad .byte 31528), (.const 0)⟩  -- jeq r3, 0, 5439
]

def iroutes5070 : List IRoute :=
  [(5053, ipre5070_5053, ipost5070_5053), (5438, ipre5070_5438, ipost5070_5438), (5995, ipre5070_5995, ipost5070_5995), (6432, ipre5070_6432, ipost5070_6432)]

theorem pins5070 : ptokenInsns.all (fun insns =>
    let m := ptAbsMap insns
    (idom5070.all (iguardCheck m) &&
      iroutes5070.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) &&
    iguardsMatch dom5070 routes5070 idom5070 iroutes5070) = true := by native_decide

/-- **Input conditions for edge 5070** (TransferChecked, native SOL). A run of p_token's decoded `.text` from
    the entrypoint, on an input described by `ptInit`, that stands at the edge started from an
    input satisfying its pinned dominating guards and one authority route's pinned guards. -/
theorem inputs5070 (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (hinit : Concrete s0 ptInit s0) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 5070) :
    (∀ ig ∈ idom5070, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes5070 ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  have hpath := check5070
  rw [hp, Option.all_some] at hpath
  have habs := absOk
  rw [hp, Option.all_some] at habs
  have hpins := pins5070
  rw [hp, Option.all_some] at hpins
  simp only [Bool.and_eq_true] at hpins
  exact edge_input_conditions _ ptNoret (ptNoret_sound insns hp) _ 198 5070 _ _ _ _ _ _ hpath
    habs (by simpa only [Bool.and_eq_true] using hpins.1) hpins.2 s0 hpc hcs hinit n hend

/-! ### Edge 5473: TransferChecked of 0 -/

def idom5473 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 }, (.inLoad .dword 20976), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 }, (.inLoad .dword 20984), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }, (.inLoad .dword 20992), (.const 10463932726783620124)⟩  -- jne r2, r3, 5717
]

def ipre5473_5053 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 }, (.inLoad .dword 128), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4725
  ⟨{ pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 }, (.inLoad .dword 136), (.inLoad .dword 31456)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 }, (.inLoad .dword 144), (.inLoad .dword 31464)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }, (.inLoad .dword 152), (.inLoad .dword 31472)⟩  -- jne r5, r3, 4725
]

def ipost5473_5053 : List IGuard := [
  ⟨{ pc := 5053, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5054 }, (.inLoad .byte 31441), (.const 0)⟩,  -- jeq r3, 0, 5716
  ⟨{ pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 }, (.inLoad .dword 20976), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 }, (.inLoad .dword 20984), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }, (.inLoad .dword 20992), (.const 10463932726783620124)⟩  -- jne r2, r3, 5717
]

def ipre5473_5438 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r3, 1, 4839
  ⟨{ pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 }, (.inLoad .dword 172), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4839
  ⟨{ pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 }, (.inLoad .dword 180), (.inLoad .dword 31456)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 }, (.inLoad .dword 188), (.inLoad .dword 31464)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }, (.inLoad .dword 196), (.inLoad .dword 31472)⟩  -- jne r0, r3, 4839
]

def ipost5473_5438 : List IGuard := [
  ⟨{ pc := 5438, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5439 }, (.inLoad .byte 31441), (.const 0)⟩,  -- jeq r3, 0, 5716
  ⟨{ pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 }, (.inLoad .dword 20976), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 }, (.inLoad .dword 20984), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }, (.inLoad .dword 20992), (.const 10463932726783620124)⟩  -- jne r2, r3, 5717
]

def ipre5473_5995 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 }, (.inLoad .dword 128), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4725
  ⟨{ pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 }, (.inLoad .dword 136), (.inLoad .dword 31456)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 }, (.inLoad .dword 144), (.inLoad .dword 31464)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }, (.inLoad .dword 152), (.inLoad .dword 31472)⟩,  -- jne r5, r3, 4725
  ⟨{ pc := 4851, insn := .jne .r4 (.imm 355) 5052, onSucc := 4852 }, (.inLoad .dword 31520), (.const 355)⟩,  -- jne r4, 355, 5052
  ⟨{ pc := 5993, insn := .jne .r4 (.imm 1) 6434, onSucc := 5994 }, (.inLoad .byte 31530), (.const 1)⟩  -- jne r4, 1, 6434
]

def ipost5473_5995 : List IGuard := [
  ⟨{ pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 }, (.inLoad .dword 20976), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 }, (.inLoad .dword 20984), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }, (.inLoad .dword 20992), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5995, insn := .jeq .r3 (.imm 0) 5054, onSucc := 5054 }, (.inLoad .byte 31528), (.const 0)⟩  -- jeq r3, 0, 5054
]

def ipre5473_6432 : List IGuard := [
  ⟨{ pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 }, (.inLoad .byte 0), (.const 3)⟩,  -- jeq r2, 3, 304
  ⟨{ pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 }, (.inLoad .byte 0), (.const 4)⟩,  -- jne r2, 4, 312
  ⟨{ pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 }, (.inLoad .dword 88), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 }, (.inLoad .byte 10512), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 }, (.inLoad .dword 10592), (.const 82)⟩,  -- jne r2, 82, 312
  ⟨{ pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 }, (.inLoad .byte 20936), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 }, (.inLoad .dword 21016), (.const 165)⟩,  -- jne r2, 165, 312
  ⟨{ pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 }, (.inLoad .byte 31440), (.const 255)⟩,  -- jne r2, 255, 312
  ⟨{ pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 }, (.inLoad .byte 204), (.const 2)⟩,  -- jgt r2, 2, 4725
  ⟨{ pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 }, (.inLoad .byte 204), (.const 0)⟩,  -- jeq r2, 0, 5080
  ⟨{ pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jgt r3, 2, 4725
  ⟨{ pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 }, (.inLoad .byte 21132), (.const 0)⟩,  -- jeq r3, 0, 5080
  ⟨{ pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 }, (.inLoad .byte 204), (.const 2)⟩,  -- jeq r2, 2, 4725
  ⟨{ pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 }, (.inLoad .byte 21132), (.const 2)⟩,  -- jeq r3, 2, 4725
  ⟨{ pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 }, (.inLoad .dword 96), (.inLoad .dword 21024)⟩,  -- jne r0, r6, 5475
  ⟨{ pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 }, (.inLoad .dword 104), (.inLoad .dword 21032)⟩,  -- jne r8, r6, 5475
  ⟨{ pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 }, (.inLoad .dword 112), (.inLoad .dword 21040)⟩,  -- jne r6, r9, 5475
  ⟨{ pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 }, (.inLoad .dword 120), (.inLoad .dword 21048)⟩,  -- jne r9, r3, 5475
  ⟨{ pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 }, (.inLoad .dword 10520), (.inLoad .dword 96)⟩,  -- jne r3, r0, 5475
  ⟨{ pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 }, (.inLoad .dword 10528), (.inLoad .dword 104)⟩,  -- jne r3, r8, 5475
  ⟨{ pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 }, (.inLoad .dword 10536), (.inLoad .dword 112)⟩,  -- jne r3, r6, 5475
  ⟨{ pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 }, (.inLoad .dword 10544), (.inLoad .dword 120)⟩,  -- jne r3, r9, 4725
  ⟨{ pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 }, (.inLoad .byte 10645), (.const 1)⟩,  -- jne r0, 1, 5078
  ⟨{ pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 }, (.inLoad .byte 168), (.const 1)⟩,  -- jne r3, 1, 4839
  ⟨{ pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 }, (.inLoad .dword 172), (.inLoad .dword 31448)⟩,  -- jne r3, r5, 4839
  ⟨{ pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 }, (.inLoad .dword 180), (.inLoad .dword 31456)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 }, (.inLoad .dword 188), (.inLoad .dword 31464)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }, (.inLoad .dword 196), (.inLoad .dword 31472)⟩,  -- jne r0, r3, 4839
  ⟨{ pc := 288, insn := .jne .r4 (.imm 355) 5437, onSucc := 289 }, (.inLoad .dword 31520), (.const 355)⟩,  -- jne r4, 355, 5437
  ⟨{ pc := 6430, insn := .jne .r4 (.imm 1) 6434, onSucc := 6431 }, (.inLoad .byte 31530), (.const 1)⟩  -- jne r4, 1, 6434
]

def ipost5473_6432 : List IGuard := [
  ⟨{ pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 }, (.inLoad .dword 48), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 }, (.inLoad .dword 56), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 }, (.inLoad .dword 64), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 }, (.inLoad .dword 72), (.const 12178014311288245306)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 }, (.inLoad .dword 20976), (.const 10637895772709248262)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 }, (.inLoad .dword 20984), (.const 12428223917890587609)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }, (.inLoad .dword 20992), (.const 10463932726783620124)⟩,  -- jne r2, r3, 5717
  ⟨{ pc := 6432, insn := .jeq .r3 (.imm 0) 5439, onSucc := 5439 }, (.inLoad .byte 31528), (.const 0)⟩  -- jeq r3, 0, 5439
]

def iroutes5473 : List IRoute :=
  [(5053, ipre5473_5053, ipost5473_5053), (5438, ipre5473_5438, ipost5473_5438), (5995, ipre5473_5995, ipost5473_5995), (6432, ipre5473_6432, ipost5473_6432)]

theorem pins5473 : ptokenInsns.all (fun insns =>
    let m := ptAbsMap insns
    (idom5473.all (iguardCheck m) &&
      iroutes5473.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) &&
    iguardsMatch dom5473 routes5473 idom5473 iroutes5473) = true := by native_decide

/-- **Input conditions for edge 5473** (TransferChecked of 0). A run of p_token's decoded `.text` from
    the entrypoint, on an input described by `ptInit`, that stands at the edge started from an
    input satisfying its pinned dominating guards and one authority route's pinned guards. -/
theorem inputs5473 (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (hinit : Concrete s0 ptInit s0) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 5473) :
    (∀ ig ∈ idom5473, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes5473 ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  have hpath := check5473
  rw [hp, Option.all_some] at hpath
  have habs := absOk
  rw [hp, Option.all_some] at habs
  have hpins := pins5473
  rw [hp, Option.all_some] at hpins
  simp only [Bool.and_eq_true] at hpins
  exact edge_input_conditions _ ptNoret (ptNoret_sound insns hp) _ 198 5473 _ _ _ _ _ _ hpath
    habs (by simpa only [Bool.and_eq_true] using hpins.1) hpins.2 s0 hpc hcs hinit n hend

end Examples.PTokenSuccessPaths
