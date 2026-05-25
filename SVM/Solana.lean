-- Solana data-model SL predicates layered on the qedsvm sBPF spec layer.
--
-- These are bundled separation-logic atoms over standard Solana account
-- formats (SPL Token, AccountInfo headers, PDA derivation results, etc.)
-- that high-level refinement theorems land against. Per-program proofs
-- import this namespace to state pre/post-conditions at the data-model
-- level rather than at the per-byte level.

import SVM.Solana.TokenAccount
import SVM.Solana.AccountInfo
import SVM.Solana.Pda
import SVM.Solana.Abstract
import SVM.Solana.Mir
import SVM.Solana.TokenAccountCodec
