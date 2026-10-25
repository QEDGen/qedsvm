/-
  Path conditions for p_token's six loop-free success edges (GENERATED; regenerate rather
  than edit). For each edge, every top-level run from the entrypoint that stands at it passed
  the guards that dominate it, then one of four authority routes with that route's own
  guards (`edge_path_condition`):

    Transfer          4825 (amount moved), 4832 (native SOL), 5250 (amount 0)
    TransferChecked   5063 (amount moved), 5070 (native SOL), 5473 (amount 0)

  Dominating guards cover the discriminator, account layout and non-duplicate markers,
  instruction length, source and destination state, `amount <= balance`, and mint equality
  (TransferChecked adds the mint account and decimals). The four routes are owner or
  delegate, each as a single signer or as a multisig. The multisig routes accept no signer
  at all: with no extra signer accounts the check reduces to `m == 0`, so they rely on the
  token program's own invariant that an initialized multisig has `m >= 1`.

  Every guard is re-checked against the decoded program by `native_decide` (`check<edge>`):
  the instruction at the guard, that its listed branch is the only one that can still reach
  the target, that it dominates the target, that the checkpoints cut every path, and that
  every set used is closed. Calls into the panic helpers have no static successor
  (`ptNoret`), justified by `panic_helpers_noReturn`.
-/
import PToken.PanicChainPins
import SVM.SBPF.PathCond

namespace Examples.PTokenSuccessPaths

open SVM.SBPF Examples.PTokenErrorTail Examples.PTokenPanicChain

/-- Call targets that never return: the entrypoint's two panic helpers. -/
def ptNoret (t : Nat) : Bool := t == 11177 || t == 10881

theorem ptNoret_sound (insns : Array Insn) (hp : ptokenInsns = some insns) :
    ∀ t, ptNoret t = true → NoReturn (Runner.fetchFromArray insns) t := by
  have h := panicCheck_ok
  rw [panicCheck, hp, Option.all_some] at h
  exact fun t ht => panic_helpers_noReturn _ (panicCheckOn_sound insns h) t ht

/-! ### Edge 4825: Transfer, amount moved (the edge's `jne r3, 1` skips the native-SOL lamport move) -/


/-- Guards every run from the entrypoint to 4825 passes. -/
def dom4825 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 }  -- jne r0, r5, 4724
]

/-- Guards from the entrypoint to checkpoint 4816. -/
def pre4825_4816 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 },  -- jne r0, r5, 4725
  { pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 },  -- jne r0, r5, 4725
  { pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 },  -- jne r0, r5, 4725
  { pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }  -- jne r0, r5, 4725
]

/-- Guards from checkpoint 4816 on to 4825. -/
def post4825_4816 : List Guard := [
  { pc := 4816, insn := .jeq .r4 (.imm 0) 5716, onSucc := 4817 },  -- jeq r4, 0, 5716
  { pc := 4817, insn := .jeq .r2 (.imm 0) 5225, onSucc := 4818 }  -- jeq r2, 0, 5225
]

/-- Guards from the entrypoint to checkpoint 5216. -/
def pre4825_5216 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 },  -- jne r0, 1, 4457
  { pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 },  -- jne r0, r5, 4457
  { pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 },  -- jne r8, r0, 4457
  { pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 },  -- jne r8, r0, 4457
  { pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }  -- jne r8, r0, 4457
]

/-- Guards from checkpoint 5216 on to 4825. -/
def post4825_5216 : List Guard := [
  { pc := 5216, insn := .jeq .r4 (.imm 0) 5716, onSucc := 5217 },  -- jeq r4, 0, 5716
  { pc := 5218, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5219 },  -- jlt r4, r2, 4725
  { pc := 5224, insn := .jne .r2 (.imm 0) 4818, onSucc := 4818 }  -- jne r2, 0, 4818
]

/-- Guards from the entrypoint to checkpoint 5715. -/
def pre4825_5715 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 },  -- jne r0, r5, 4725
  { pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 },  -- jne r0, r5, 4725
  { pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 },  -- jne r0, r5, 4725
  { pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 },  -- jne r0, r5, 4725
  { pc := 4469, insn := .jne .r4 (.imm 355) 4815, onSucc := 4470 },  -- jne r4, 355, 4815
  { pc := 5713, insn := .jne .r4 (.imm 1) 6235, onSucc := 5714 }  -- jne r4, 1, 6235
]

/-- Guards from checkpoint 5715 on to 4825. -/
def post4825_5715 : List Guard := [
  { pc := 4817, insn := .jeq .r2 (.imm 0) 5225, onSucc := 4818 },  -- jeq r2, 0, 5225
  { pc := 5715, insn := .jeq .r4 (.imm 0) 4817, onSucc := 4817 }  -- jeq r4, 0, 4817
]

/-- Guards from the entrypoint to checkpoint 6233. -/
def pre4825_6233 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 },  -- jne r0, 1, 4457
  { pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 },  -- jne r0, r5, 4457
  { pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 },  -- jne r8, r0, 4457
  { pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 },  -- jne r8, r0, 4457
  { pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 },  -- jne r8, r0, 4457
  { pc := 4043, insn := .jne .r4 (.imm 355) 5215, onSucc := 4044 },  -- jne r4, 355, 5215
  { pc := 6231, insn := .jne .r4 (.imm 1) 6235, onSucc := 6232 }  -- jne r4, 1, 6235
]

/-- Guards from checkpoint 6233 on to 4825. -/
def post4825_6233 : List Guard := [
  { pc := 5218, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5219 },  -- jlt r4, r2, 4725
  { pc := 5224, insn := .jne .r2 (.imm 0) 4818, onSucc := 4818 },  -- jne r2, 0, 4818
  { pc := 6233, insn := .jeq .r4 (.imm 0) 5217, onSucc := 5217 }  -- jeq r4, 0, 5217
]

/-- Edge 4825's authority routes. -/
def routes4825 : List Route :=
  [(4816, pre4825_4816, post4825_4816), (5216, pre4825_5216, post4825_5216), (5715, pre4825_5715, post4825_5715), (6233, pre4825_6233, post4825_6233)]

theorem check4825 : ptokenInsns.all (fun insns =>
    edgeCheck (Runner.fetchFromArray insns) ptNoret insns.size 198 4825 dom4825 routes4825) = true := by
  native_decide

/-- Path condition for edge 4825 (Transfer, amount moved (the edge's `jne r3, 1` skips the native-SOL lamport move)). -/
theorem path4825 (insns : Array Insn) (hp : ptokenInsns = some insns) (s : State)
    (hpc : s.pc = 198) (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s n).pc = 4825) :
    let f := Runner.fetchFromArray insns
    PassedGuards f s n dom4825 ∧
    ∃ c pre post, (c, pre, post) ∈ routes4825 ∧ ∃ j, j ≤ n ∧
      (executeFn f s j).callStack = [] ∧ (executeFn f s j).exitCode = none ∧
      (executeFn f s j).pc = c ∧ PassedGuards f s j pre ∧
      PassedGuards f (executeFn f s j) (n - j) post := by
  have h := check4825
  rw [hp, Option.all_some] at h
  exact edge_path_condition _ ptNoret (ptNoret_sound insns hp) _ 198 4825 _ _ h s hpc hcs n hend

/-! ### Edge 4832: Transfer, native SOL account (also moves lamports) -/


/-- Guards every run from the entrypoint to 4832 passes. -/
def dom4832 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 }  -- jne r3, 1, 3542
]

/-- Guards from the entrypoint to checkpoint 4816. -/
def pre4832_4816 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 },  -- jne r0, r5, 4725
  { pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 },  -- jne r0, r5, 4725
  { pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 },  -- jne r0, r5, 4725
  { pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }  -- jne r0, r5, 4725
]

/-- Guards from checkpoint 4816 on to 4832. -/
def post4832_4816 : List Guard := [
  { pc := 4816, insn := .jeq .r4 (.imm 0) 5716, onSucc := 4817 },  -- jeq r4, 0, 5716
  { pc := 4817, insn := .jeq .r2 (.imm 0) 5225, onSucc := 4818 },  -- jeq r2, 0, 5225
  { pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 }  -- jne r3, 1, 3542
]

/-- Guards from the entrypoint to checkpoint 5216. -/
def pre4832_5216 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 },  -- jne r0, 1, 4457
  { pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 },  -- jne r0, r5, 4457
  { pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 },  -- jne r8, r0, 4457
  { pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 },  -- jne r8, r0, 4457
  { pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }  -- jne r8, r0, 4457
]

/-- Guards from checkpoint 5216 on to 4832. -/
def post4832_5216 : List Guard := [
  { pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 },  -- jne r3, 1, 3542
  { pc := 5216, insn := .jeq .r4 (.imm 0) 5716, onSucc := 5217 },  -- jeq r4, 0, 5716
  { pc := 5218, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5219 },  -- jlt r4, r2, 4725
  { pc := 5224, insn := .jne .r2 (.imm 0) 4818, onSucc := 4818 }  -- jne r2, 0, 4818
]

/-- Guards from the entrypoint to checkpoint 5715. -/
def pre4832_5715 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 },  -- jne r0, r5, 4725
  { pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 },  -- jne r0, r5, 4725
  { pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 },  -- jne r0, r5, 4725
  { pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 },  -- jne r0, r5, 4725
  { pc := 4469, insn := .jne .r4 (.imm 355) 4815, onSucc := 4470 },  -- jne r4, 355, 4815
  { pc := 5713, insn := .jne .r4 (.imm 1) 6235, onSucc := 5714 }  -- jne r4, 1, 6235
]

/-- Guards from checkpoint 5715 on to 4832. -/
def post4832_5715 : List Guard := [
  { pc := 4817, insn := .jeq .r2 (.imm 0) 5225, onSucc := 4818 },  -- jeq r2, 0, 5225
  { pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 },  -- jne r3, 1, 3542
  { pc := 5715, insn := .jeq .r4 (.imm 0) 4817, onSucc := 4817 }  -- jeq r4, 0, 4817
]

/-- Guards from the entrypoint to checkpoint 6233. -/
def pre4832_6233 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 },  -- jne r0, 1, 4457
  { pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 },  -- jne r0, r5, 4457
  { pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 },  -- jne r8, r0, 4457
  { pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 },  -- jne r8, r0, 4457
  { pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 },  -- jne r8, r0, 4457
  { pc := 4043, insn := .jne .r4 (.imm 355) 5215, onSucc := 4044 },  -- jne r4, 355, 5215
  { pc := 6231, insn := .jne .r4 (.imm 1) 6235, onSucc := 6232 }  -- jne r4, 1, 6235
]

/-- Guards from checkpoint 6233 on to 4832. -/
def post4832_6233 : List Guard := [
  { pc := 4825, insn := .jne .r3 (.imm 1) 3542, onSucc := 4826 },  -- jne r3, 1, 3542
  { pc := 5218, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5219 },  -- jlt r4, r2, 4725
  { pc := 5224, insn := .jne .r2 (.imm 0) 4818, onSucc := 4818 },  -- jne r2, 0, 4818
  { pc := 6233, insn := .jeq .r4 (.imm 0) 5217, onSucc := 5217 }  -- jeq r4, 0, 5217
]

/-- Edge 4832's authority routes. -/
def routes4832 : List Route :=
  [(4816, pre4832_4816, post4832_4816), (5216, pre4832_5216, post4832_5216), (5715, pre4832_5715, post4832_5715), (6233, pre4832_6233, post4832_6233)]

theorem check4832 : ptokenInsns.all (fun insns =>
    edgeCheck (Runner.fetchFromArray insns) ptNoret insns.size 198 4832 dom4832 routes4832) = true := by
  native_decide

/-- Path condition for edge 4832 (Transfer, native SOL account (also moves lamports)). -/
theorem path4832 (insns : Array Insn) (hp : ptokenInsns = some insns) (s : State)
    (hpc : s.pc = 198) (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s n).pc = 4832) :
    let f := Runner.fetchFromArray insns
    PassedGuards f s n dom4832 ∧
    ∃ c pre post, (c, pre, post) ∈ routes4832 ∧ ∃ j, j ≤ n ∧
      (executeFn f s j).callStack = [] ∧ (executeFn f s j).exitCode = none ∧
      (executeFn f s j).pc = c ∧ PassedGuards f s j pre ∧
      PassedGuards f (executeFn f s j) (n - j) post := by
  have h := check4832
  rw [hp, Option.all_some] at h
  exact edge_path_condition _ ptNoret (ptNoret_sound insns hp) _ 198 4832 _ _ h s hpc hcs n hend

/-! ### Edge 5250: Transfer of 0: both accounts owned by the token program -/


/-- Guards every run from the entrypoint to 5250 passes. -/
def dom5250 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 },  -- jne r2, r3, 5717
  { pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 },  -- jne r2, r3, 5717
  { pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 },  -- jne r2, r3, 5717
  { pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 },  -- jne r2, r3, 5717
  { pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 },  -- jne r2, r3, 5717
  { pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 },  -- jne r2, r3, 5717
  { pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }  -- jne r2, r3, 5717
]

/-- Guards from the entrypoint to checkpoint 4816. -/
def pre5250_4816 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 },  -- jne r0, r5, 4725
  { pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 },  -- jne r0, r5, 4725
  { pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 },  -- jne r0, r5, 4725
  { pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 }  -- jne r0, r5, 4725
]

/-- Guards from checkpoint 4816 on to 5250. -/
def post5250_4816 : List Guard := [
  { pc := 4816, insn := .jeq .r4 (.imm 0) 5716, onSucc := 4817 },  -- jeq r4, 0, 5716
  { pc := 4817, insn := .jeq .r2 (.imm 0) 5225, onSucc := 5225 },  -- jeq r2, 0, 5225
  { pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 },  -- jne r2, r3, 5717
  { pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 },  -- jne r2, r3, 5717
  { pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 },  -- jne r2, r3, 5717
  { pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 },  -- jne r2, r3, 5717
  { pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 },  -- jne r2, r3, 5717
  { pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 },  -- jne r2, r3, 5717
  { pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }  -- jne r2, r3, 5717
]

/-- Guards from the entrypoint to checkpoint 5216. -/
def pre5250_5216 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 },  -- jne r0, 1, 4457
  { pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 },  -- jne r0, r5, 4457
  { pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 },  -- jne r8, r0, 4457
  { pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 },  -- jne r8, r0, 4457
  { pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 }  -- jne r8, r0, 4457
]

/-- Guards from checkpoint 5216 on to 5250. -/
def post5250_5216 : List Guard := [
  { pc := 5216, insn := .jeq .r4 (.imm 0) 5716, onSucc := 5217 },  -- jeq r4, 0, 5716
  { pc := 5218, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5219 },  -- jlt r4, r2, 4725
  { pc := 5224, insn := .jne .r2 (.imm 0) 4818, onSucc := 5225 },  -- jne r2, 0, 4818
  { pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 },  -- jne r2, r3, 5717
  { pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 },  -- jne r2, r3, 5717
  { pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 },  -- jne r2, r3, 5717
  { pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 },  -- jne r2, r3, 5717
  { pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 },  -- jne r2, r3, 5717
  { pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 },  -- jne r2, r3, 5717
  { pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 }  -- jne r2, r3, 5717
]

/-- Guards from the entrypoint to checkpoint 5715. -/
def pre5250_5715 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4459, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4460 },  -- jne r0, r5, 4725
  { pc := 4462, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4463 },  -- jne r0, r5, 4725
  { pc := 4465, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4466 },  -- jne r0, r5, 4725
  { pc := 4468, insn := .jne .r0 (.reg .r5) 4725, onSucc := 4469 },  -- jne r0, r5, 4725
  { pc := 4469, insn := .jne .r4 (.imm 355) 4815, onSucc := 4470 },  -- jne r4, 355, 4815
  { pc := 5713, insn := .jne .r4 (.imm 1) 6235, onSucc := 5714 }  -- jne r4, 1, 6235
]

/-- Guards from checkpoint 5715 on to 5250. -/
def post5250_5715 : List Guard := [
  { pc := 4817, insn := .jeq .r2 (.imm 0) 5225, onSucc := 5225 },  -- jeq r2, 0, 5225
  { pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 },  -- jne r2, r3, 5717
  { pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 },  -- jne r2, r3, 5717
  { pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 },  -- jne r2, r3, 5717
  { pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 },  -- jne r2, r3, 5717
  { pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 },  -- jne r2, r3, 5717
  { pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 },  -- jne r2, r3, 5717
  { pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 },  -- jne r2, r3, 5717
  { pc := 5715, insn := .jeq .r4 (.imm 0) 4817, onSucc := 4817 }  -- jeq r4, 0, 4817
]

/-- Guards from the entrypoint to checkpoint 6233. -/
def pre5250_6233 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 304 },  -- jeq r2, 3, 304
  { pc := 305, insn := .jne .r2 (.imm 165) 312, onSucc := 306 },  -- jne r2, 165, 312
  { pc := 307, insn := .jne .r2 (.imm 255) 312, onSucc := 308 },  -- jne r2, 255, 312
  { pc := 309, insn := .jne .r2 (.imm 165) 312, onSucc := 310 },  -- jne r2, 165, 312
  { pc := 311, insn := .jeq .r2 (.imm 255) 3991, onSucc := 3991 },  -- jeq r2, 255, 3991
  { pc := 3998, insn := .jlt .r3 (.imm 9) 312, onSucc := 3999 },  -- jlt r3, 9, 312
  { pc := 4000, insn := .jne .r3 (.imm 3) 312, onSucc := 4001 },  -- jne r3, 3, 312
  { pc := 4004, insn := .jgt .r3 (.imm 2) 4725, onSucc := 4005 },  -- jgt r3, 2, 4725
  { pc := 4005, insn := .jeq .r3 (.imm 0) 5080, onSucc := 4006 },  -- jeq r3, 0, 5080
  { pc := 4007, insn := .jgt .r5 (.imm 2) 4725, onSucc := 4008 },  -- jgt r5, 2, 4725
  { pc := 4008, insn := .jeq .r5 (.imm 0) 5080, onSucc := 4009 },  -- jeq r5, 0, 5080
  { pc := 4011, insn := .jeq .r3 (.imm 2) 4725, onSucc := 4012 },  -- jeq r3, 2, 4725
  { pc := 4012, insn := .jeq .r5 (.imm 2) 4725, onSucc := 4013 },  -- jeq r5, 2, 4725
  { pc := 4016, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 4017 },  -- jlt r3, r2, 4725
  { pc := 4019, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4020 },  -- jne r0, r5, 4724
  { pc := 4022, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4023 },  -- jne r0, r5, 4724
  { pc := 4025, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4026 },  -- jne r0, r5, 4724
  { pc := 4028, insn := .jne .r0 (.reg .r5) 4724, onSucc := 4029 },  -- jne r0, r5, 4724
  { pc := 4031, insn := .jne .r0 (.imm 1) 4457, onSucc := 4032 },  -- jne r0, 1, 4457
  { pc := 4033, insn := .jne .r0 (.reg .r5) 4457, onSucc := 4034 },  -- jne r0, r5, 4457
  { pc := 4036, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4037 },  -- jne r8, r0, 4457
  { pc := 4039, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4040 },  -- jne r8, r0, 4457
  { pc := 4042, insn := .jne .r8 (.reg .r0) 4457, onSucc := 4043 },  -- jne r8, r0, 4457
  { pc := 4043, insn := .jne .r4 (.imm 355) 5215, onSucc := 4044 },  -- jne r4, 355, 5215
  { pc := 6231, insn := .jne .r4 (.imm 1) 6235, onSucc := 6232 }  -- jne r4, 1, 6235
]

/-- Guards from checkpoint 6233 on to 5250. -/
def post5250_6233 : List Guard := [
  { pc := 5218, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5219 },  -- jlt r4, r2, 4725
  { pc := 5224, insn := .jne .r2 (.imm 0) 4818, onSucc := 5225 },  -- jne r2, 0, 4818
  { pc := 5228, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5229 },  -- jne r2, r3, 5717
  { pc := 5231, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5232 },  -- jne r2, r3, 5717
  { pc := 5234, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5235 },  -- jne r2, r3, 5717
  { pc := 5237, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5238 },  -- jne r2, r3, 5717
  { pc := 5240, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5241 },  -- jne r2, r3, 5717
  { pc := 5243, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5244 },  -- jne r2, r3, 5717
  { pc := 5246, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5247 },  -- jne r2, r3, 5717
  { pc := 6233, insn := .jeq .r4 (.imm 0) 5217, onSucc := 5217 }  -- jeq r4, 0, 5217
]

/-- Edge 5250's authority routes. -/
def routes5250 : List Route :=
  [(4816, pre5250_4816, post5250_4816), (5216, pre5250_5216, post5250_5216), (5715, pre5250_5715, post5250_5715), (6233, pre5250_6233, post5250_6233)]

theorem check5250 : ptokenInsns.all (fun insns =>
    edgeCheck (Runner.fetchFromArray insns) ptNoret insns.size 198 5250 dom5250 routes5250) = true := by
  native_decide

/-- Path condition for edge 5250 (Transfer of 0: both accounts owned by the token program). -/
theorem path5250 (insns : Array Insn) (hp : ptokenInsns = some insns) (s : State)
    (hpc : s.pc = 198) (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s n).pc = 5250) :
    let f := Runner.fetchFromArray insns
    PassedGuards f s n dom5250 ∧
    ∃ c pre post, (c, pre, post) ∈ routes5250 ∧ ∃ j, j ≤ n ∧
      (executeFn f s j).callStack = [] ∧ (executeFn f s j).exitCode = none ∧
      (executeFn f s j).pc = c ∧ PassedGuards f s j pre ∧
      PassedGuards f (executeFn f s j) (n - j) post := by
  have h := check5250
  rw [hp, Option.all_some] at h
  exact edge_path_condition _ ptNoret (ptNoret_sound insns hp) _ 198 5250 _ _ h s hpc hcs n hend

/-! ### Edge 5063: TransferChecked, amount moved -/


/-- Guards every run from the entrypoint to 5063 passes. -/
def dom5063 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 }  -- jne r3, r5, 5990
]

/-- Guards from the entrypoint to checkpoint 5053. -/
def pre5063_5053 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 },  -- jne r3, r5, 4725
  { pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 },  -- jne r5, r3, 4725
  { pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 },  -- jne r5, r3, 4725
  { pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }  -- jne r5, r3, 4725
]

/-- Guards from checkpoint 5053 on to 5063. -/
def post5063_5053 : List Guard := [
  { pc := 5053, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5054 },  -- jeq r3, 0, 5716
  { pc := 5054, insn := .jeq .r2 (.imm 0) 5448, onSucc := 5055 }  -- jeq r2, 0, 5448
]

/-- Guards from the entrypoint to checkpoint 5438. -/
def pre5063_5438 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 },  -- jne r3, 1, 4839
  { pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 },  -- jne r3, r5, 4839
  { pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 },  -- jne r0, r3, 4839
  { pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 },  -- jne r0, r3, 4839
  { pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }  -- jne r0, r3, 4839
]

/-- Guards from checkpoint 5438 on to 5063. -/
def post5063_5438 : List Guard := [
  { pc := 5438, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5439 },  -- jeq r3, 0, 5716
  { pc := 5441, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5442 },  -- jlt r4, r2, 4725
  { pc := 5447, insn := .jne .r2 (.imm 0) 5055, onSucc := 5055 }  -- jne r2, 0, 5055
]

/-- Guards from the entrypoint to checkpoint 5995. -/
def pre5063_5995 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 },  -- jne r3, r5, 4725
  { pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 },  -- jne r5, r3, 4725
  { pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 },  -- jne r5, r3, 4725
  { pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 },  -- jne r5, r3, 4725
  { pc := 4851, insn := .jne .r4 (.imm 355) 5052, onSucc := 4852 },  -- jne r4, 355, 5052
  { pc := 5993, insn := .jne .r4 (.imm 1) 6434, onSucc := 5994 }  -- jne r4, 1, 6434
]

/-- Guards from checkpoint 5995 on to 5063. -/
def post5063_5995 : List Guard := [
  { pc := 5054, insn := .jeq .r2 (.imm 0) 5448, onSucc := 5055 },  -- jeq r2, 0, 5448
  { pc := 5995, insn := .jeq .r3 (.imm 0) 5054, onSucc := 5054 }  -- jeq r3, 0, 5054
]

/-- Guards from the entrypoint to checkpoint 6432. -/
def pre5063_6432 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 },  -- jne r3, 1, 4839
  { pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 },  -- jne r3, r5, 4839
  { pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 },  -- jne r0, r3, 4839
  { pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 },  -- jne r0, r3, 4839
  { pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 },  -- jne r0, r3, 4839
  { pc := 288, insn := .jne .r4 (.imm 355) 5437, onSucc := 289 },  -- jne r4, 355, 5437
  { pc := 6430, insn := .jne .r4 (.imm 1) 6434, onSucc := 6431 }  -- jne r4, 1, 6434
]

/-- Guards from checkpoint 6432 on to 5063. -/
def post5063_6432 : List Guard := [
  { pc := 5441, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5442 },  -- jlt r4, r2, 4725
  { pc := 5447, insn := .jne .r2 (.imm 0) 5055, onSucc := 5055 },  -- jne r2, 0, 5055
  { pc := 6432, insn := .jeq .r3 (.imm 0) 5439, onSucc := 5439 }  -- jeq r3, 0, 5439
]

/-- Edge 5063's authority routes. -/
def routes5063 : List Route :=
  [(5053, pre5063_5053, post5063_5053), (5438, pre5063_5438, post5063_5438), (5995, pre5063_5995, post5063_5995), (6432, pre5063_6432, post5063_6432)]

theorem check5063 : ptokenInsns.all (fun insns =>
    edgeCheck (Runner.fetchFromArray insns) ptNoret insns.size 198 5063 dom5063 routes5063) = true := by
  native_decide

/-- Path condition for edge 5063 (TransferChecked, amount moved). -/
theorem path5063 (insns : Array Insn) (hp : ptokenInsns = some insns) (s : State)
    (hpc : s.pc = 198) (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s n).pc = 5063) :
    let f := Runner.fetchFromArray insns
    PassedGuards f s n dom5063 ∧
    ∃ c pre post, (c, pre, post) ∈ routes5063 ∧ ∃ j, j ≤ n ∧
      (executeFn f s j).callStack = [] ∧ (executeFn f s j).exitCode = none ∧
      (executeFn f s j).pc = c ∧ PassedGuards f s j pre ∧
      PassedGuards f (executeFn f s j) (n - j) post := by
  have h := check5063
  rw [hp, Option.all_some] at h
  exact edge_path_condition _ ptNoret (ptNoret_sound insns hp) _ 198 5063 _ _ h s hpc hcs n hend

/-! ### Edge 5070: TransferChecked, native SOL account -/


/-- Guards every run from the entrypoint to 5070 passes. -/
def dom5070 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 }  -- jne r3, 1, 3542
]

/-- Guards from the entrypoint to checkpoint 5053. -/
def pre5070_5053 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 },  -- jne r3, r5, 4725
  { pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 },  -- jne r5, r3, 4725
  { pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 },  -- jne r5, r3, 4725
  { pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }  -- jne r5, r3, 4725
]

/-- Guards from checkpoint 5053 on to 5070. -/
def post5070_5053 : List Guard := [
  { pc := 5053, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5054 },  -- jeq r3, 0, 5716
  { pc := 5054, insn := .jeq .r2 (.imm 0) 5448, onSucc := 5055 },  -- jeq r2, 0, 5448
  { pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 }  -- jne r3, 1, 3542
]

/-- Guards from the entrypoint to checkpoint 5438. -/
def pre5070_5438 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 },  -- jne r3, 1, 4839
  { pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 },  -- jne r3, r5, 4839
  { pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 },  -- jne r0, r3, 4839
  { pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 },  -- jne r0, r3, 4839
  { pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }  -- jne r0, r3, 4839
]

/-- Guards from checkpoint 5438 on to 5070. -/
def post5070_5438 : List Guard := [
  { pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 },  -- jne r3, 1, 3542
  { pc := 5438, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5439 },  -- jeq r3, 0, 5716
  { pc := 5441, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5442 },  -- jlt r4, r2, 4725
  { pc := 5447, insn := .jne .r2 (.imm 0) 5055, onSucc := 5055 }  -- jne r2, 0, 5055
]

/-- Guards from the entrypoint to checkpoint 5995. -/
def pre5070_5995 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 },  -- jne r3, r5, 4725
  { pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 },  -- jne r5, r3, 4725
  { pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 },  -- jne r5, r3, 4725
  { pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 },  -- jne r5, r3, 4725
  { pc := 4851, insn := .jne .r4 (.imm 355) 5052, onSucc := 4852 },  -- jne r4, 355, 5052
  { pc := 5993, insn := .jne .r4 (.imm 1) 6434, onSucc := 5994 }  -- jne r4, 1, 6434
]

/-- Guards from checkpoint 5995 on to 5070. -/
def post5070_5995 : List Guard := [
  { pc := 5054, insn := .jeq .r2 (.imm 0) 5448, onSucc := 5055 },  -- jeq r2, 0, 5448
  { pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 },  -- jne r3, 1, 3542
  { pc := 5995, insn := .jeq .r3 (.imm 0) 5054, onSucc := 5054 }  -- jeq r3, 0, 5054
]

/-- Guards from the entrypoint to checkpoint 6432. -/
def pre5070_6432 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 },  -- jne r3, 1, 4839
  { pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 },  -- jne r3, r5, 4839
  { pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 },  -- jne r0, r3, 4839
  { pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 },  -- jne r0, r3, 4839
  { pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 },  -- jne r0, r3, 4839
  { pc := 288, insn := .jne .r4 (.imm 355) 5437, onSucc := 289 },  -- jne r4, 355, 5437
  { pc := 6430, insn := .jne .r4 (.imm 1) 6434, onSucc := 6431 }  -- jne r4, 1, 6434
]

/-- Guards from checkpoint 6432 on to 5070. -/
def post5070_6432 : List Guard := [
  { pc := 5063, insn := .jne .r3 (.imm 1) 3542, onSucc := 5064 },  -- jne r3, 1, 3542
  { pc := 5441, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5442 },  -- jlt r4, r2, 4725
  { pc := 5447, insn := .jne .r2 (.imm 0) 5055, onSucc := 5055 },  -- jne r2, 0, 5055
  { pc := 6432, insn := .jeq .r3 (.imm 0) 5439, onSucc := 5439 }  -- jeq r3, 0, 5439
]

/-- Edge 5070's authority routes. -/
def routes5070 : List Route :=
  [(5053, pre5070_5053, post5070_5053), (5438, pre5070_5438, post5070_5438), (5995, pre5070_5995, post5070_5995), (6432, pre5070_6432, post5070_6432)]

theorem check5070 : ptokenInsns.all (fun insns =>
    edgeCheck (Runner.fetchFromArray insns) ptNoret insns.size 198 5070 dom5070 routes5070) = true := by
  native_decide

/-- Path condition for edge 5070 (TransferChecked, native SOL account). -/
theorem path5070 (insns : Array Insn) (hp : ptokenInsns = some insns) (s : State)
    (hpc : s.pc = 198) (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s n).pc = 5070) :
    let f := Runner.fetchFromArray insns
    PassedGuards f s n dom5070 ∧
    ∃ c pre post, (c, pre, post) ∈ routes5070 ∧ ∃ j, j ≤ n ∧
      (executeFn f s j).callStack = [] ∧ (executeFn f s j).exitCode = none ∧
      (executeFn f s j).pc = c ∧ PassedGuards f s j pre ∧
      PassedGuards f (executeFn f s j) (n - j) post := by
  have h := check5070
  rw [hp, Option.all_some] at h
  exact edge_path_condition _ ptNoret (ptNoret_sound insns hp) _ 198 5070 _ _ h s hpc hcs n hend

/-! ### Edge 5473: TransferChecked of 0: both accounts owned by the token program -/


/-- Guards every run from the entrypoint to 5473 passes. -/
def dom5473 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 },  -- jne r2, r3, 5717
  { pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 },  -- jne r2, r3, 5717
  { pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 },  -- jne r2, r3, 5717
  { pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 },  -- jne r2, r3, 5717
  { pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 },  -- jne r2, r3, 5717
  { pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 },  -- jne r2, r3, 5717
  { pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }  -- jne r2, r3, 5717
]

/-- Guards from the entrypoint to checkpoint 5053. -/
def pre5473_5053 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 },  -- jne r3, r5, 4725
  { pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 },  -- jne r5, r3, 4725
  { pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 },  -- jne r5, r3, 4725
  { pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 }  -- jne r5, r3, 4725
]

/-- Guards from checkpoint 5053 on to 5473. -/
def post5473_5053 : List Guard := [
  { pc := 5053, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5054 },  -- jeq r3, 0, 5716
  { pc := 5054, insn := .jeq .r2 (.imm 0) 5448, onSucc := 5448 },  -- jeq r2, 0, 5448
  { pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 },  -- jne r2, r3, 5717
  { pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 },  -- jne r2, r3, 5717
  { pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 },  -- jne r2, r3, 5717
  { pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 },  -- jne r2, r3, 5717
  { pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 },  -- jne r2, r3, 5717
  { pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 },  -- jne r2, r3, 5717
  { pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }  -- jne r2, r3, 5717
]

/-- Guards from the entrypoint to checkpoint 5438. -/
def pre5473_5438 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 },  -- jne r3, 1, 4839
  { pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 },  -- jne r3, r5, 4839
  { pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 },  -- jne r0, r3, 4839
  { pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 },  -- jne r0, r3, 4839
  { pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 }  -- jne r0, r3, 4839
]

/-- Guards from checkpoint 5438 on to 5473. -/
def post5473_5438 : List Guard := [
  { pc := 5438, insn := .jeq .r3 (.imm 0) 5716, onSucc := 5439 },  -- jeq r3, 0, 5716
  { pc := 5441, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5442 },  -- jlt r4, r2, 4725
  { pc := 5447, insn := .jne .r2 (.imm 0) 5055, onSucc := 5448 },  -- jne r2, 0, 5055
  { pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 },  -- jne r2, r3, 5717
  { pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 },  -- jne r2, r3, 5717
  { pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 },  -- jne r2, r3, 5717
  { pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 },  -- jne r2, r3, 5717
  { pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 },  -- jne r2, r3, 5717
  { pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 },  -- jne r2, r3, 5717
  { pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 }  -- jne r2, r3, 5717
]

/-- Guards from the entrypoint to checkpoint 5995. -/
def pre5473_5995 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 4841, insn := .jne .r3 (.reg .r5) 4725, onSucc := 4842 },  -- jne r3, r5, 4725
  { pc := 4844, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4845 },  -- jne r5, r3, 4725
  { pc := 4847, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4848 },  -- jne r5, r3, 4725
  { pc := 4850, insn := .jne .r5 (.reg .r3) 4725, onSucc := 4851 },  -- jne r5, r3, 4725
  { pc := 4851, insn := .jne .r4 (.imm 355) 5052, onSucc := 4852 },  -- jne r4, 355, 5052
  { pc := 5993, insn := .jne .r4 (.imm 1) 6434, onSucc := 5994 }  -- jne r4, 1, 6434
]

/-- Guards from checkpoint 5995 on to 5473. -/
def post5473_5995 : List Guard := [
  { pc := 5054, insn := .jeq .r2 (.imm 0) 5448, onSucc := 5448 },  -- jeq r2, 0, 5448
  { pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 },  -- jne r2, r3, 5717
  { pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 },  -- jne r2, r3, 5717
  { pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 },  -- jne r2, r3, 5717
  { pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 },  -- jne r2, r3, 5717
  { pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 },  -- jne r2, r3, 5717
  { pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 },  -- jne r2, r3, 5717
  { pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 },  -- jne r2, r3, 5717
  { pc := 5995, insn := .jeq .r3 (.imm 0) 5054, onSucc := 5054 }  -- jeq r3, 0, 5054
]

/-- Guards from the entrypoint to checkpoint 6432. -/
def pre5473_6432 : List Guard := [
  { pc := 199, insn := .jeq .r2 (.imm 3) 304, onSucc := 200 },  -- jeq r2, 3, 304
  { pc := 200, insn := .jne .r2 (.imm 4) 312, onSucc := 201 },  -- jne r2, 4, 312
  { pc := 202, insn := .jne .r2 (.imm 165) 312, onSucc := 203 },  -- jne r2, 165, 312
  { pc := 204, insn := .jne .r2 (.imm 255) 312, onSucc := 205 },  -- jne r2, 255, 312
  { pc := 206, insn := .jne .r2 (.imm 82) 312, onSucc := 207 },  -- jne r2, 82, 312
  { pc := 208, insn := .jne .r2 (.imm 255) 312, onSucc := 209 },  -- jne r2, 255, 312
  { pc := 210, insn := .jne .r2 (.imm 165) 312, onSucc := 211 },  -- jne r2, 165, 312
  { pc := 212, insn := .jne .r2 (.imm 255) 312, onSucc := 213 },  -- jne r2, 255, 312
  { pc := 222, insn := .jlt .r2 (.imm 10) 312, onSucc := 223 },  -- jlt r2, 10, 312
  { pc := 226, insn := .jne .r2 (.imm 12) 312, onSucc := 227 },  -- jne r2, 12, 312
  { pc := 230, insn := .jgt .r2 (.imm 2) 4725, onSucc := 231 },  -- jgt r2, 2, 4725
  { pc := 231, insn := .jeq .r2 (.imm 0) 5080, onSucc := 232 },  -- jeq r2, 0, 5080
  { pc := 233, insn := .jgt .r3 (.imm 2) 4725, onSucc := 234 },  -- jgt r3, 2, 4725
  { pc := 234, insn := .jeq .r3 (.imm 0) 5080, onSucc := 235 },  -- jeq r3, 0, 5080
  { pc := 237, insn := .jeq .r2 (.imm 2) 4725, onSucc := 238 },  -- jeq r2, 2, 4725
  { pc := 238, insn := .jeq .r3 (.imm 2) 4725, onSucc := 239 },  -- jeq r3, 2, 4725
  { pc := 244, insn := .jlt .r3 (.reg .r2) 4725, onSucc := 245 },  -- jlt r3, r2, 4725
  { pc := 248, insn := .jne .r0 (.reg .r6) 5475, onSucc := 249 },  -- jne r0, r6, 5475
  { pc := 251, insn := .jne .r8 (.reg .r6) 5475, onSucc := 252 },  -- jne r8, r6, 5475
  { pc := 255, insn := .jne .r6 (.reg .r9) 5475, onSucc := 256 },  -- jne r6, r9, 5475
  { pc := 258, insn := .jne .r9 (.reg .r3) 5475, onSucc := 259 },  -- jne r9, r3, 5475
  { pc := 260, insn := .jne .r3 (.reg .r0) 5475, onSucc := 261 },  -- jne r3, r0, 5475
  { pc := 262, insn := .jne .r3 (.reg .r8) 5475, onSucc := 263 },  -- jne r3, r8, 5475
  { pc := 264, insn := .jne .r3 (.reg .r6) 5475, onSucc := 265 },  -- jne r3, r6, 5475
  { pc := 267, insn := .jne .r3 (.reg .r9) 4725, onSucc := 268 },  -- jne r3, r9, 4725
  { pc := 269, insn := .jne .r0 (.imm 1) 5078, onSucc := 270 },  -- jne r0, 1, 5078
  { pc := 273, insn := .jne .r3 (.reg .r5) 5990, onSucc := 274 },  -- jne r3, r5, 5990
  { pc := 276, insn := .jne .r3 (.imm 1) 4839, onSucc := 277 },  -- jne r3, 1, 4839
  { pc := 278, insn := .jne .r3 (.reg .r5) 4839, onSucc := 279 },  -- jne r3, r5, 4839
  { pc := 281, insn := .jne .r0 (.reg .r3) 4839, onSucc := 282 },  -- jne r0, r3, 4839
  { pc := 284, insn := .jne .r0 (.reg .r3) 4839, onSucc := 285 },  -- jne r0, r3, 4839
  { pc := 287, insn := .jne .r0 (.reg .r3) 4839, onSucc := 288 },  -- jne r0, r3, 4839
  { pc := 288, insn := .jne .r4 (.imm 355) 5437, onSucc := 289 },  -- jne r4, 355, 5437
  { pc := 6430, insn := .jne .r4 (.imm 1) 6434, onSucc := 6431 }  -- jne r4, 1, 6434
]

/-- Guards from checkpoint 6432 on to 5473. -/
def post5473_6432 : List Guard := [
  { pc := 5441, insn := .jlt .r4 (.reg .r2) 4725, onSucc := 5442 },  -- jlt r4, r2, 4725
  { pc := 5447, insn := .jne .r2 (.imm 0) 5055, onSucc := 5448 },  -- jne r2, 0, 5055
  { pc := 5451, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5452 },  -- jne r2, r3, 5717
  { pc := 5454, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5455 },  -- jne r2, r3, 5717
  { pc := 5457, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5458 },  -- jne r2, r3, 5717
  { pc := 5460, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5461 },  -- jne r2, r3, 5717
  { pc := 5463, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5464 },  -- jne r2, r3, 5717
  { pc := 5466, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5467 },  -- jne r2, r3, 5717
  { pc := 5469, insn := .jne .r2 (.reg .r3) 5717, onSucc := 5470 },  -- jne r2, r3, 5717
  { pc := 6432, insn := .jeq .r3 (.imm 0) 5439, onSucc := 5439 }  -- jeq r3, 0, 5439
]

/-- Edge 5473's authority routes. -/
def routes5473 : List Route :=
  [(5053, pre5473_5053, post5473_5053), (5438, pre5473_5438, post5473_5438), (5995, pre5473_5995, post5473_5995), (6432, pre5473_6432, post5473_6432)]

theorem check5473 : ptokenInsns.all (fun insns =>
    edgeCheck (Runner.fetchFromArray insns) ptNoret insns.size 198 5473 dom5473 routes5473) = true := by
  native_decide

/-- Path condition for edge 5473 (TransferChecked of 0: both accounts owned by the token program). -/
theorem path5473 (insns : Array Insn) (hp : ptokenInsns = some insns) (s : State)
    (hpc : s.pc = 198) (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s n).pc = 5473) :
    let f := Runner.fetchFromArray insns
    PassedGuards f s n dom5473 ∧
    ∃ c pre post, (c, pre, post) ∈ routes5473 ∧ ∃ j, j ≤ n ∧
      (executeFn f s j).callStack = [] ∧ (executeFn f s j).exitCode = none ∧
      (executeFn f s j).pc = c ∧ PassedGuards f s j pre ∧
      PassedGuards f (executeFn f s j) (n - j) post := by
  have h := check5473
  rw [hp, Option.all_some] at h
  exact edge_path_condition _ ptNoret (ptNoret_sound insns hp) _ 198 5473 _ _ h s hpc hcs n hend


end Examples.PTokenSuccessPaths
