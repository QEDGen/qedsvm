-- WP tactics for sBPF proof automation: wp_exec (one-shot), wp_step
-- (single instruction, for manual proofs).

import SVM.SBPF.Execute

namespace SVM.SBPF

/-! ## wp_exec — one-shot sBPF verification

Proves `(executeFn progAt (initState inputAddr mem) FUEL).exitCode = some CODE`.
First bracket: fetch fn + chunk defs (→ dsimp for decode). Second bracket:
effectiveAddr lemmas + extras (→ simp for branch resolution). It switches to
monadic execution, unfolds execSegment one step at a time (O(1) kernel
depth), dsimps the fetch, simps branches, and rfls the halted residual.

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
          [initState, execInsn, chargeCu, Width.bytes,
           RegFile.get, RegFile.set, resolveSrc, readByWidth, $[$fetch],*];
        simp (config := { failIfUnchanged := false }) [*, $[$extras],*]);
      rfl))

/-! ## wp_step — single instruction step (for manual proofs)

Unfolds one execSegment level, dsimps the instruction, simps with
hypotheses. Use when wp_exec needs manual guidance between steps
(e.g. memory disjointness lemmas). -/

open Lean.Parser.Tactic in
syntax "wp_step" "[" simpLemma,* "]" "[" simpLemma,* "]" : tactic

set_option hygiene false in
open Lean.Parser.Tactic in
macro_rules
  | `(tactic| wp_step [$[$fetch:simpLemma],*] [$[$extras:simpLemma],*]) => `(tactic| (
      unfold execSegment;
      dsimp (config := { failIfUnchanged := false })
        [initState, execInsn, chargeCu, Width.bytes,
         RegFile.get, RegFile.set, resolveSrc, readByWidth, $[$fetch],*];
      simp (config := { failIfUnchanged := false }) [*, $[$extras],*]))

/-! ## strip_writes — automatic memory write stripping

Strips nested write layers from reads by proving address disjointness via
omega. Pre-unfolds STACK_START so omega sees pure numerals. Handles both
cross-region (input read through stack write) and within-stack reads.

Usage (after a wp_step left read-through-write patterns):
  wp_step [progAt, progAt_0, progAt_1, writeByWidth] [ea_offsets...]
  strip_writes
  simp [h_read_hypothesis, *]

Normalize wrapAdd/toU64 in hypotheses first (`simp [wrapAdd, toU64] at h_addr`).
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

Like strip_writes but unfolds STACK_START in the goal only, not hypotheses.
Use when many hypotheses (20+ wp_step calls) make `unfold … at *` time out. -/

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

Rewrites with a chain of memory hypotheses, then region-based frame
reasoning to strip write layers from reads. `rewrite_mem [hmem]` ≡
`rw [hmem]; mem_frame`.
-/

open Lean.Parser.Tactic in
syntax "rewrite_mem" "[" rwRule,* "]" : tactic

set_option hygiene false in
open Lean.Parser.Tactic in
open SVM.SBPF.Memory in
macro_rules
  | `(tactic| rewrite_mem [$[$ts:rwRule],*]) => `(tactic| (
      rw [$[$ts],*];
      -- Goal only (collapsed hmem can be huge).
      try unfold STACK_START;
      repeat (first
        -- Frame: read below stack, write above (the common sBPF case).
        | rw [readU64_writeU64_frame _ _ _ _ (by omega) (by omega)]
        | rw [readU8_writeU64_frame _ _ _ _ (by omega) (by omega)]
        -- Disjointness fallback (same region or mixed widths).
        | rw [readU64_writeU64_disjoint _ _ _ _ (by omega)]
        | rw [readU8_writeU64_outside _ _ _ _ (by omega)]
        | rw [readU64_writeU8_disjoint _ _ _ _ (by omega)]
        -- Same-address round-trip.
        | rw [readU64_writeU64_same _ _ _ (by first | simp | omega)])))

/-! ## solve_read — one-shot memory read resolution

`rewrite_mem` to strip write layers, then close with `exact`.
Usage: `solve_read [hmem] h_val`.
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

A *symbolic* table closes by hypothesis rewrite (the `Patterns.lean`
idiom). A *concrete* table (list literal, e.g. unfolded `runtimeRegions n`)
plus address bounds is mechanical: unfold the fold, bool-disjunction →
props, `omega` picks the covering region. The optional bracket takes the
defs revealing the table (table def + address-space constants).

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

Splits a long run into phase windows composed with `executeFn_compose`:
unrolling `wp_step` N times to *reach* step N blows kernel depth, but the
compose rewrite is O(1). `wp_exec_from k m` rewrites
`executeFn fetch s (k + m)` (fuel matched up to defeq, so `76` matches
`36 + 40`) into `executeFn fetch (executeFn fetch s k) m`; the `using h`
form also rewrites the inner window with `h : executeFn fetch s k = s'`.

Usage:
  wp_exec_from 36 40 using hphase1   -- goal now `executeFn fetch s' 40`
-/

syntax "wp_exec_from" term:max term:max ("using" term)? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wp_exec_from $k $m) =>
      `(tactic| rw [executeFn_compose _ _ $k $m])
  | `(tactic| wp_exec_from $k $m using $h) =>
      `(tactic| rw [executeFn_compose _ _ $k $m, $h:term])

/-! ## Regression: `wp_exec` must reduce `Width.bytes` itself

The region check at every `ldx`/`st`/`stx` compares against `w.bytes`.
Unless the macro's dsimp list reduces this plain def, `Width.dword.bytes`
never becomes `8`, the coverage hypothesis never matches, the `if` never
resolves, and the trailing `rfl` whnf-explodes into a heartbeat timeout
(QEDGen/solana-skills#86, #32). This proves a load through a *symbolic*
table without `Width.bytes` in extras; the low budget fails fast in CI. -/

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

A `runtimeRegions`-shaped literal table + a symbolic bounded address:
coverage and writable-coverage both close mechanically. -/

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

The fuel literal `4` must match `2 + 2` up to defeq for the compose
rewrite, and the `using` form must rewrite the inner window with a phase
lemma (here built from `executeFn_step` + `executeFn_zero`). -/

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
      = chargeCu (step (.mov64 .r2 (.imm 7)) (initState inputAddr mem rt)) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step _ _ 0 _ rfl (Nat.zero_le _) rfl, executeFn_zero]
  wp_exec_from 1 3 using hphase
  wp_exec [phaseSplitProg, step] []

end SVM.SBPF
