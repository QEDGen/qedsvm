/-
  qedsvm side of the solanalib differential oracle (SPIKE).

  Speaks the SAME stdin/stdout contract as solanalib's `sbpf-oracle`
  (leanprover-solanalib, `Oracle.lean`), so a corpus can be fed to both
  and the outputs diffed line-for-line.

  INPUT  (one test vector per line, space-separated decimals):
      <version> <fuel> <byte0> <byte1> ...
  OUTPUT (one line per input line):
      ok <r0>      -- program EXITed at depth 0 with r0 = <r0> (clean exit)
      fault        -- runtime fault, fuel/budget exhaustion, or fell off code
      reject       -- qedsvm-only: decode refused the program (verifier fold)
      error: ...   -- input parse failure

  qedsvm folds agave's verifier rejections into `decode` (fail-closed),
  whereas solanalib runs a verifier-less interpreter, so `reject` is a
  qedsvm-specific outcome the diff harness buckets separately from `fault`.

  We model SBPFv1 (neg / mul / div / mod live in the base ALU; no PQR,
  no byteswap), so drive solanalib with `version = 1`.

  Initial state mirrors solanalib's oracle: zeroed registers, empty
  memory, register-only computation. (qedsvm's r10 default is 0, while
  solanalib seats r10 at the stack top; the corpus avoids reading r10,
  so the constant never becomes observable.)
-/

import SVM.SBPF.Runner

open SVM.SBPF

namespace DiffOracle

/-- Split a line into non-empty whitespace-separated tokens. -/
def tokens (line : String) : List String :=
  let normalized := ((line.replace "\t" " ").replace "\r" " ")
  (normalized.splitOn " ").filter (· ≠ "")

/-- Fold decimal byte tokens into a `ByteArray`; `none` on a non-numeric or
    out-of-range (>255) token. -/
def bytesOfTokens : List String → Option ByteArray :=
  go ByteArray.empty
where
  go (acc : ByteArray) : List String → Option ByteArray
    | [] => some acc
    | t :: rest =>
      match t.toNat? with
      | some n => if n < 256 then go (acc.push (UInt8.ofNat n)) rest else none
      | none   => none

/-- Parse one input line into `(version, fuel, programBytes)`. -/
def parseLine (line : String) : Option (Nat × Nat × ByteArray) :=
  match tokens line with
  | ver :: fuelS :: rest =>
    match ver.toNat?, fuelS.toNat?, bytesOfTokens rest with
    | some v, some fuel, some bytes => some (v, fuel, bytes)
    | _, _, _ => none
  | _ => none

/-- Run one decoded program from a zeroed state and classify the outcome. -/
def runOne (fuel : Nat) (bytes : ByteArray) : String :=
  match Decode.decodeProgram bytes [] with
  | none => "reject"
  | some insns =>
    -- Zeroed registers, empty memory, no mapped regions (memory ops trap,
    -- matching solanalib's empty-memory faults). cuBudget set to `fuel`
    -- and executeFn's recursion bound set to `fuel`, so neither the CU
    -- meter nor the step bound fires before a quick-terminating program.
    let s0 : State :=
      { regs := {}, mem := Runner.emptyMem, regions := [], pc := 0,
        cuBudget := fuel }
    let s := executeFn (Runner.fetchFromArray insns) s0 fuel
    match s.exitCode, s.vmError with
    | some n, none => s!"ok {n}"        -- clean exit (typed-fault channel empty)
    | _,      _    => "fault"            -- fault / out-of-budget / fell off code

def classify (line : String) : String :=
  match parseLine line with
  | some (_v, fuel, bytes) => runOne fuel bytes
  | none => "error: parse"

end DiffOracle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let content ← stdin.readToEnd
  let mut out : Array String := #[]
  for rawLine in content.splitOn "\n" do
    -- skip blank / whitespace-only lines; `tokens` filters empties
    if !(DiffOracle.tokens rawLine).isEmpty then
      out := out.push (DiffOracle.classify rawLine)
  IO.println (String.intercalate "\n" out.toList)
