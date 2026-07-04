-- Solana Pattern Proof Library, Layer 3: guards (check enforcement).
--
-- The security-relevant unit on Solana is not a state predicate but a GUARD: the
-- program reads a field, compares it, and faults (does not perform the effect)
-- when the check is violated, on every path. The dominant exploit class is a
-- missing or wrong guard. So the library's center of gravity is here, not in the
-- predicates: predicates and recognizers are the supporting vocabulary, guards
-- are the product.
--
-- Two distinct properties, easy to conflate:
--   * "REQUIRES": a refinement's precondition assumes the check passed (the spec
--     is conditional on it). The proven AsmRefinesToken* arms are like this: they
--     state the data transformation on the happy path and assume nothing faults.
--   * "ENFORCES": the program itself diverts to a fault when the check is
--     violated. This is the security property. The bug (missing check) is exactly
--     REQUIRES-without-ENFORCES: a path that reaches the effect without the check.
--
-- We express ENFORCES over the typed-fault channel (`VmError` / `State.vmError`),
-- reusing the `cuTripleFaultsWithin*` triples and their sequencing lemmas. The
-- notion lives here (SVM lib); concrete instantiations against proven p_token
-- bytecode live in the Examples lib (which may import the SVM lib, not vice
-- versa), harvested from the `TransferArm` check windows.

import SVM.SBPF.CPSSpec
import SVM.SBPF.ExitTriple

namespace SVM.Solana.Patterns

open SVM.SBPF

/-- A check is ENFORCED by the code window at `entry` if, from any state where the
    check is VIOLATED (`viol`), the window faults with typed error `e` within its
    CU budget. Faulting means `exitCode = some e.toSentinel` and `vmError = some e`
    (a real VM fault, not a clean program-returned error), so the effect is never
    reached on the violating branch.

    This is the Layer-3 security property the pattern library targets. It is
    strictly stronger than a refinement precondition that merely assumes the
    check. -/
def EnforcedFault (nSteps nCu entry : Nat) (cr : CodeReq)
    (viol : Assertion) (rr : Memory.RegionTable → Prop) (e : VmError) : Prop :=
  cuTripleFaultsWithinMem nSteps nCu entry cr viol rr e

/-- The canonical way to prove a guard: show the violated check ROUTES from
    `entry` to the error handler at `errPc` (a `cuTripleWithinMem`), then reuse the
    handler's own fault spec (a `cuTripleFaultsWithin` from `errPc`). The two
    compose into full enforcement. Thin wrapper over the existing
    `cuTripleWithinMem_seq_fault_pure`, named for the guard vocabulary.

    The routing half is the substantive, program-specific obligation (the program
    actually diverts on a violated check); the handler-fault half is a generic,
    reusable fact about the program's shared error exit. -/
theorem enforcedFault_of_routes_then_handler
    {N1 N2 M1 M2 entry errPc : Nat} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2) {viol mid : Assertion}
    {rr1 : Memory.RegionTable → Prop} {e : VmError}
    (hroute : cuTripleWithinMem N1 M1 entry errPc cr1 viol mid rr1)
    (hfault : cuTripleFaultsWithin N2 M2 errPc cr2 mid e) :
    EnforcedFault (N1 + N2) (M1 + M2) entry (cr1.union cr2) viol rr1 e :=
  cuTripleWithinMem_seq_fault_pure hd hroute hfault

/-- The CLEAN-EXIT enforcement mode, `EnforcedFault`'s sibling: from a
    violating state the window runs to the program's shared `.exit` and HALTS
    with the NONZERO error code `code` (`exitCode = some code`) — the effect
    is never reached, and agave fails the instruction on the nonzero return.
    Pinocchio-style programs enforce checks this way (a `TokenError` routed
    through the error handler into `r0`), rather than VM-faulting; `post`
    carries the untouched protected cells through to the halt.

    The concrete instance (`Examples`,
    `PToken.TransferArm.BalanceGuardEnforced`) composes the mechanically
    lifted p-token Transfer ERROR PATH (`PTokenTransferInsufficient_lifted_spec`,
    qedlift over a violating trace) with the shared exit via
    `cuTripleWithinMem_seq_exit`. -/
def EnforcedError (nSteps nCu entry : Nat) (cr : CodeReq)
    (viol post : Assertion) (rr : Memory.RegionTable → Prop)
    (code : Nat) : Prop :=
  code ≠ 0 ∧ cuTripleExitsWithinMem nSteps nCu entry cr viol post rr code

end SVM.Solana.Patterns
