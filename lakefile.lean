import Lake
open Lake DSL

-- formal-svm — Lean 4 reference semantics for the Solana Virtual Machine.
--
-- Pure Lean 4, no Mathlib dependency. Anything that needs Mathlib-level
-- reasoning (`Fin → α`, `BigOperators`, ring/omega over closed forms)
-- belongs in a downstream consumer, not here.
--
-- Scope (F1, reference semantics):
--   Svm.Account — Pubkey and Account data model
--   Svm.Cpi     — invoke_signed envelope, well-known program IDs, discriminators
--   Svm.SBPF.*  — sBPF interpreter (ISA, Memory, Execute, WP tactic)
--
-- See README.md and docs/founding-rationale.md for scope and roadmap.
package formalSvm

@[default_target]
lean_lib Svm where
  roots := #[`Svm]
