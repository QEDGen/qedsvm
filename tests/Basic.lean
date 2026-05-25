import SVM

-- Basic smoke tests for the SVM package.
-- Real proof patterns live in downstream consumers; this just verifies
-- that the public surface is wired up correctly.

open SVM

-- Pubkey reflexivity
example (k : Pubkey) : k = k := rfl

-- TOKEN_PROGRAM_ID is a concrete Pubkey
example : TOKEN_PROGRAM_ID = TOKEN_PROGRAM_ID := rfl

-- A well-formed CpiInstruction passes envelope predicates
example :
    targetsProgram
      { programId := TOKEN_PROGRAM_ID
      , accounts := [⟨⟨1, 0, 0, 0⟩, true, false⟩]
      , data := DISC_TRANSFER }
      TOKEN_PROGRAM_ID := by
  unfold targetsProgram SVM.Cpi.targetsProgram
  rfl

-- Discriminator prefix check
example :
    hasDiscriminator
      { programId := TOKEN_PROGRAM_ID
      , accounts := []
      , data := DISC_TRANSFER ++ [1, 2, 3] }
      DISC_TRANSFER := by
  unfold hasDiscriminator SVM.Cpi.hasDiscriminator
  decide
