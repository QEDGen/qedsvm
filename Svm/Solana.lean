-- Solana data-model SL predicates layered on the qedsvm sBPF spec layer.
--
-- These are bundled separation-logic atoms over standard Solana account
-- formats (SPL Token, AccountInfo headers, PDA derivation results, etc.)
-- that high-level refinement theorems land against. Per-program proofs
-- import this namespace to state pre/post-conditions at the data-model
-- level rather than at the per-byte level.

import Svm.Solana.TokenAccount
import Svm.Solana.AccountInfo
import Svm.Solana.Pda
