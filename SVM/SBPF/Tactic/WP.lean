-- WP tactics for sBPF proof automation
--
-- wp_exec: one-shot tactic for sBPF property proofs
-- wp_step: single instruction step (for manual proofs)

import SVM.SBPF.Execute

namespace SVM.SBPF

/-! ## wp_exec — one-shot sBPF verification

Proves properties of the form:
  (executeFn progAt (initState inputAddr mem) FUEL).exitCode = some CODE

Usage:
  wp_exec [progAt, progAt_0, progAt_1] [ea_0, ea_88]

First bracket: fetch function + chunk defs (passed to dsimp for instruction decode).
Second bracket: effectiveAddr lemmas + extras (passed to simp for branch resolution).

The tactic:
1. Applies executeFn_eq_execSegment to switch to monadic execution
2. Iteratively unfolds execSegment one step at a time (O(1) kernel depth)
3. Uses dsimp to evaluate instruction fetch via kernel reduction
4. Uses simp with hypotheses to resolve branch conditions
5. Closes the halted-state residual via rfl

Example:
  theorem rejects_bad_input ... := by
    have h1 : ¬(readU64 mem inputAddr = EXPECTED) := by ...
    wp_exec [progAt, progAt_0] [ea_0]
-/

open Lean.Parser.Tactic in
syntax "wp_exec" "[" simpLemma,* "]" "[" simpLemma,* "]" : tactic

set_option hygiene false in
open Lean.Parser.Tactic in
macro_rules
  | `(tactic| wp_exec [$[$fetch:simpLemma],*] [$[$extras:simpLemma],*]) => `(tactic| (
      rw [executeFn_eq_execSegment];
      repeat (
        unfold execSegment;
        dsimp (config := { failIfUnchanged := false })
          [initState, execInsn, Width.bytes,
           RegFile.get, RegFile.set, resolveSrc, readByWidth, $[$fetch],*];
        simp (config := { failIfUnchanged := false }) [*, $[$extras],*]);
      rfl))

/-! ## wp_step — single instruction step (for manual proofs)

Unfolds one level of execSegment, evaluates the instruction via dsimp,
and simplifies with hypotheses. Use when wp_exec needs manual guidance
(e.g., memory disjointness lemmas between steps). -/

open Lean.Parser.Tactic in
syntax "wp_step" "[" simpLemma,* "]" "[" simpLemma,* "]" : tactic

set_option hygiene false in
open Lean.Parser.Tactic in
macro_rules
  | `(tactic| wp_step [$[$fetch:simpLemma],*] [$[$extras:simpLemma],*]) => `(tactic| (
      unfold execSegment;
      dsimp (config := { failIfUnchanged := false })
        [initState, execInsn, Width.bytes,
         RegFile.get, RegFile.set, resolveSrc, readByWidth, $[$fetch],*];
      simp (config := { failIfUnchanged := false }) [*, $[$extras],*]))

/-! ## strip_writes — automatic memory write stripping

Strips nested write layers from read expressions by proving address disjointness
via omega. Pre-unfolds STACK_START so omega sees pure numerals.

Works for both cross-region (input reads through stack writes) and
within-stack (stack reads at different offsets from stack writes).

Usage (after a wp_step that left read-through-write patterns in the goal):
  wp_step [progAt, progAt_0, progAt_1, writeByWidth] [ea_offsets...]
  strip_writes
  simp [h_read_hypothesis, *]

For hypotheses containing wrapAdd/toU64, normalize them first:
  simp [wrapAdd, toU64] at h_addr
  strip_writes
-/

open SVM.SBPF.Memory in
syntax "strip_writes" : tactic

set_option hygiene false in
open SVM.SBPF.Memory in
macro_rules
  | `(tactic| strip_writes) => `(tactic| (
    try unfold STACK_START at *;
    repeat (first
      | rw [readU64_writeU64_disjoint _ _ _ _ (by omega)]
      | rw [readU8_writeU64_outside _ _ _ _ (by omega)]
      | rw [readU64_writeU8_disjoint _ _ _ _ (by omega)]
      | rw [readU64_writeU64_same _ _ _ (by first | simp | omega)])))

/-! ## strip_writes_goal — goal-only variant for large contexts

Like strip_writes but only unfolds STACK_START in the goal, not hypotheses.
Use this when the context has many hypotheses (e.g., after 20+ wp_step calls)
and `unfold STACK_START at *` causes timeout. -/

open SVM.SBPF.Memory in
syntax "strip_writes_goal" : tactic

set_option hygiene false in
open SVM.SBPF.Memory in
macro_rules
  | `(tactic| strip_writes_goal) => `(tactic| (
    try unfold STACK_START;
    repeat (first
      | rw [readU64_writeU64_disjoint _ _ _ _ (by omega)]
      | rw [readU8_writeU64_outside _ _ _ _ (by omega)]
      | rw [readU64_writeU8_disjoint _ _ _ _ (by omega)]
      | rw [readU64_writeU64_same _ _ _ (by first | simp | omega)])))

/-! ## rewrite_mem — rewrite memory chain + frame

Rewrites with a chain of memory hypotheses, then applies region-based
frame reasoning to strip write layers from read expressions.

Usage:
  rewrite_mem [hmem]

is equivalent to:
  rw [hmem]; mem_frame
-/

open Lean.Parser.Tactic in
syntax "rewrite_mem" "[" rwRule,* "]" : tactic

set_option hygiene false in
open Lean.Parser.Tactic in
open SVM.SBPF.Memory in
macro_rules
  | `(tactic| rewrite_mem [$[$ts:rwRule],*]) => `(tactic| (
      rw [$[$ts],*];
      -- Unfold STACK_START in goal only (not hypotheses — collapsed hmem can be huge)
      try unfold STACK_START;
      repeat (first
        -- Frame: read below stack, write above stack (most common in sBPF)
        | rw [readU64_writeU64_frame _ _ _ _ (by omega) (by omega)]
        | rw [readU8_writeU64_frame _ _ _ _ (by omega) (by omega)]
        -- Disjointness fallback (within same region or mixed widths)
        | rw [readU64_writeU64_disjoint _ _ _ _ (by omega)]
        | rw [readU8_writeU64_outside _ _ _ _ (by omega)]
        | rw [readU64_writeU8_disjoint _ _ _ _ (by omega)]
        -- Same-address round-trip
        | rw [readU64_writeU64_same _ _ _ (by first | simp | omega)])))

/-! ## solve_read — one-shot memory read resolution

Rewrites with a chain of memory hypotheses, applies frame reasoning
to strip write layers, then closes the goal with `exact`.

Usage:
  solve_read [hmem] h_val
-/

open Lean.Parser.Tactic in
syntax "solve_read" "[" rwRule,* "]" term : tactic

set_option hygiene false in
open Lean.Parser.Tactic in
open SVM.SBPF.Memory in
macro_rules
  | `(tactic| solve_read [$[$ts:rwRule],*] $closing) => `(tactic| (
      rewrite_mem [$[$ts],*];
      exact $closing))

/-! ## region_covers — discharge concrete region-coverage checks (#32 item 2)

With a *symbolic* region table, coverage closes by hypothesis rewrite
(the `Patterns.lean` idiom). With a *concrete* table (a list literal,
e.g. `runtimeRegions n` after unfolding) plus address bounds in
context, the check is mechanical: unfold the table fold, turn the
boolean disjunction into propositions, and let `omega` pick the
covering region. The optional bracket takes the defs that reveal the
table (the table def itself plus address-space constants).

Usage:
  region_covers                          -- table already a literal
  region_covers [runtimeRegions, Memory.STACK_START]
-/

open Lean.Parser.Tactic in
syntax "region_covers" ("[" simpLemma,* "]")? : tactic

set_option hygiene false in
open Lean.Parser.Tactic in
macro_rules
  | `(tactic| region_covers) => `(tactic| (
      simp only [Memory.RegionTable.containsRange,
        Memory.RegionTable.containsWritable, Memory.Region.contains,
        List.any_cons, List.any_nil, Bool.or_eq_true, Bool.and_eq_true,
        Bool.or_false, Bool.false_or, Bool.true_and, Bool.false_and,
        decide_eq_true_eq];
      omega))
  | `(tactic| region_covers [$[$defs:simpLemma],*]) => `(tactic| (
      simp (config := { failIfUnchanged := false }) only [$[$defs],*] at *;
      region_covers))

/-! ## wp_exec_from — phase-window split (#32 item 3)

The phased / skeleton-first proof discipline splits a long run into
windows: prove each phase as its own lemma, compose with
`executeFn_compose`. Unrolling `wp_step` N times to *reach* step N
blows kernel depth; the compose rewrite is O(1). This is the tactic
wrapper that was previously hand-written at every phase boundary.

`wp_exec_from k m` rewrites a goal about `executeFn fetch s (k + m)`
(the fuel literal is matched up to defeq, so `76` matches `36 + 40`)
into one about `executeFn fetch (executeFn fetch s k) m`. The `using h`
form additionally rewrites the inner window with the phase lemma
`h : executeFn fetch s k = s'`.

Usage:
  wp_exec_from 36 40 using hphase1
  -- goal is now about `executeFn fetch s' 40`; continue with wp_exec
  -- or the next phase.
-/

syntax "wp_exec_from" term:max term:max ("using" term)? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wp_exec_from $k $m) =>
      `(tactic| rw [executeFn_compose _ _ $k $m])
  | `(tactic| wp_exec_from $k $m using $h) =>
      `(tactic| rw [executeFn_compose _ _ $k $m, $h:term])

/-! ## Regression: `wp_exec` must reduce `Width.bytes` itself

The region check at every `ldx`/`st`/`stx` step compares against
`w.bytes`. `Width.bytes` is a plain def, so unless the macro's dsimp
list reduces it, `Width.dword.bytes` never becomes `8`, a coverage
hypothesis like `rt.containsRange addr 8 = true` never matches, the
`if` never resolves, and the trailing `rfl` whnf-explodes into a
heartbeat timeout (QEDGen/solana-skills#86, #32). This theorem proves a
load through a *symbolic* region table without `Width.bytes` in the
extras list; the low heartbeat budget makes a regression fail fast
instead of hanging CI. -/

private def widthBytesRegressionProg : Nat → Option Insn
  | 0 => some (.ldx .dword .r2 .r1 0)
  | 1 => some .exit
  | _ => none

set_option maxHeartbeats 400000 in
private theorem wp_exec_reduces_width_bytes
    (inputAddr : Nat) (mem : Memory.Mem) (rt : Memory.RegionTable)
    (h_rt : rt.containsRange (Memory.effectiveAddr inputAddr 0) 8 = true) :
    (executeFn widthBytesRegressionProg
      (initState inputAddr mem rt) 2).exitCode = some 0 := by
  open SVM.SBPF.Memory in
  wp_exec [widthBytesRegressionProg] []

/-! ## Regression: `region_covers` on a concrete table

A `runtimeRegions`-shaped literal table (stack + heap + input), a
symbolic address with bounds: coverage and writable-coverage both
close mechanically. -/

private def regionCoversTestTable (inputLen : Nat) : Memory.RegionTable :=
  [ { start := Memory.STACK_START, size := 0x1000 * 64, writable := true }
  , { start := Memory.HEAP_START,  size := 0x8000,      writable := true }
  , { start := Memory.INPUT_START, size := inputLen,    writable := false } ]

private theorem region_covers_concrete_table
    (inputLen addr : Nat)
    (h_lo : Memory.INPUT_START ≤ addr)
    (h_hi : addr + 8 ≤ Memory.INPUT_START + inputLen) :
    (regionCoversTestTable inputLen).containsRange addr 8 = true := by
  region_covers [regionCoversTestTable, Memory.INPUT_START]

private theorem region_covers_writable
    (inputLen addr : Nat)
    (h_lo : Memory.HEAP_START ≤ addr)
    (h_hi : addr + 8 ≤ Memory.HEAP_START + 0x8000) :
    (regionCoversTestTable inputLen).containsWritable addr 8 = true := by
  region_covers [regionCoversTestTable, Memory.HEAP_START, Memory.INPUT_START]

/-! ## Regression: `wp_exec_from` splits the fuel literal

The fuel literal (`4`) must match `2 + 2` up to defeq for the compose
rewrite to fire, and the `using` form must rewrite the inner window
with a phase lemma. The phase lemma here is itself produced by
`executeFn_step` + `executeFn_zero` (the manual idiom the tactic's
phased discipline composes with). -/

private def phaseSplitProg : Nat → Option Insn
  | 0 => some (.mov64 .r2 (.imm 7))
  | 1 => some (.add64 .r2 (.imm 1))
  | 2 => some (.mov64 .r0 (.imm 0))
  | 3 => some .exit
  | _ => none

private theorem wp_exec_from_splits
    (inputAddr : Nat) (mem : Memory.Mem) (rt : Memory.RegionTable) :
    (executeFn phaseSplitProg (initState inputAddr mem rt) 4).exitCode
      = some 0 := by
  wp_exec_from 2 2
  wp_exec [phaseSplitProg] []

private theorem wp_exec_from_using_phase_lemma
    (inputAddr : Nat) (mem : Memory.Mem) (rt : Memory.RegionTable) :
    (executeFn phaseSplitProg (initState inputAddr mem rt) 4).exitCode
      = some 0 := by
  have hphase : executeFn phaseSplitProg (initState inputAddr mem rt) 1
      = step (.mov64 .r2 (.imm 7)) (initState inputAddr mem rt) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step _ _ 0 _ rfl rfl, executeFn_zero]
  wp_exec_from 1 3 using hphase
  wp_exec [phaseSplitProg, step] []

end SVM.SBPF
