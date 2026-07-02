/-
  Whole-transition obligations (#40, gap 1) — the asm-side shape a compiled
  program must take to refine one PATH of a `.qedspec` handler transition.

  A handler denotes `Transition : State → Args → Option State`: a guard
  cascade, a multi-field effect, and N abort paths each tied to an error
  code. Its refinement decomposes per PATH: under each path's guard
  hypotheses (meta-level binders on the emitted theorem — the trace-guided
  lift's `h_branch*` certificates), the program TERMINATES with that path's
  exit code, its tracked account codecs transitioning pre→post:

  * success path: `code = 0`, `postFields` carry the effect;
  * abort path: `code` = the spec's error code, and each account is
    instantiated with `preFields = postFields` — preservation is
    syntactically evident in the statement.

  The whole transition is the conjunction of its path obligations (the
  emitted theorem is an `And` of guard-implications). Same seam discipline
  as `AsmRefinesFieldUpdates` (#25): neutral structures only — field lists,
  exit codes — no knowledge of qedgen's `State` shape.
-/

import SVM.SBPF.ExitTriple
import SVM.Solana.Abstract.Refinement

namespace SVM.Solana.Abstract

open SVM.SBPF

/-- One path of a whole-transition refinement: a TERMINATING
    (`cuTripleExitsWithinMem`) analog of `AsmRefinesFieldUpdates` — the
    program exits with `exitCode = some code` and the accounts' coarse
    codecs go pre→post. The post leads with the exit channel (`r0 = code`,
    empty call stack) so `cuTripleWithinMem_seq_exit` discharges the shape
    syntactically from a lifted running triple plus the shared `.exit`. -/
def AsmRefinesTransitionPath
    (cr : CodeReq) (nSteps nCu entry : Nat)
    (rr : Memory.RegionTable → Prop) (code : Nat)
    (accts : List AccountFields)
    (setupPre setupPost : Assertion) : Prop :=
  cuTripleExitsWithinMem nSteps nCu entry cr
    (setupPre ** codecsPre accts)
    ((.r0 ↦ᵣ code) ** callStackIs [] ** setupPost ** codecsPost accts)
    rr code

/-- One FAULT path of a whole-transition refinement: under this path's guard
    hypotheses the program faults with the typed `e` — `exitCode =
    some e.toSentinel` AND `vmError = some e` (audit L1's channel) — from a
    pre owning the tracked account codecs. `cuTripleFaultsWithinMem`
    deliberately carries no partial-state post: at the chain level a faulted
    instruction is rolled back wholesale, so a fault path's meaningful
    content is the typed error channel, not the final VM memory. Compose a
    lifted running prefix with the terminal fault spec via
    `cuTripleWithinMem_seq_fault_pure` to discharge it. -/
def AsmRefinesTransitionFault
    (cr : CodeReq) (nSteps nCu entry : Nat)
    (rr : Memory.RegionTable → Prop) (e : VmError)
    (accts : List AccountFields)
    (setupPre : Assertion) : Prop :=
  cuTripleFaultsWithinMem nSteps nCu entry cr
    (setupPre ** codecsPre accts)
    rr e

end SVM.Solana.Abstract
