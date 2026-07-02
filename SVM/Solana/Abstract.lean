-- Abstract Solana state + asm-side refinement obligations, layered above the
-- sBPF byte-level model. `State` holds decoded account records; `Refinement`
-- declares the `AsmRefines…` predicates the discharge route reshapes to a
-- layout-general field-list obligation.

import SVM.Solana.Abstract.State
import SVM.Solana.Abstract.Refinement
import SVM.Solana.Abstract.Transition
