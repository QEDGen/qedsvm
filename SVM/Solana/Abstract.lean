-- Abstract Solana state + the asm-side refinement obligations.
--
-- Layered above the sBPF byte-level model: `State` holds the decoded
-- account records (TokenAccount, Mint, CounterAccount); `Refinement`
-- declares the `AsmRefines…` obligation predicates a compiled program
-- must meet, the input the discharge route reshapes to a layout-general
-- field-list obligation. See `Abstract/State.lean` for the layering
-- rationale and the extension protocol for new fields.

import SVM.Solana.Abstract.State
import SVM.Solana.Abstract.Refinement
