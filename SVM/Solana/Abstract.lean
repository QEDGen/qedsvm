-- Abstract Solana state + separation logic + refinement bridge.
--
-- Layered above the sBPF byte-level model: reasoning here is over
-- decoded records (TokenAccount, ...) rather than byte ranges. See
-- `Abstract/State.lean` for the layering rationale and the extension
-- protocol for new fields.

import SVM.Solana.Abstract.State
import SVM.Solana.Abstract.SepLogic
import SVM.Solana.Abstract.Triples
import SVM.Solana.Abstract.Refinement
import SVM.Solana.Abstract.Domain
import SVM.Solana.Abstract.Footprint
import SVM.Solana.Abstract.Abi
