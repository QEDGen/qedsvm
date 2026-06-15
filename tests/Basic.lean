import SVM

-- Smoke tests: verify the public surface is wired up.

open SVM

example (k : Pubkey) : k = k := rfl

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

example :
    hasDiscriminator
      { programId := TOKEN_PROGRAM_ID
      , accounts := []
      , data := DISC_TRANSFER ++ [1, 2, 3] }
      DISC_TRANSFER := by
  unfold hasDiscriminator SVM.Cpi.hasDiscriminator
  decide
