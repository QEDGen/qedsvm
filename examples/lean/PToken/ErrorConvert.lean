/-
  p_token fn 116: pinocchio's `ProgramError -> u64` conversion, the function the shared error
  tail (PCs 3536-3541) calls right before the program's single exit (PC 3542). GENERATED from
  the recovered decision tree (`qed_analysis::cfg`); every node is a branch join over disjoint
  subtrees, so the post value `convVal` mirrors the bytecode's tree exactly.

  `convVal_ne_zero`: the conversion never yields 0, so no error path can exit with success.
-/
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenErrorConvert

open SVM.SBPF

set_option maxRecDepth 8192

/-- Distribute a join's assertion-level `if` into the register value. -/
theorem ite_post {c : Prop} [Decidable c] (r : Reg) {a a' : Nat} {F : Assertion} :
    ∀ h, (if c then (r ↦ᵣ a) ** F else (r ↦ᵣ a') ** F) h → ((r ↦ᵣ (if c then a else a')) ** F) h := by
  intro h hh
  by_cases hc : c
  · rw [if_pos hc] at hh; rw [if_pos hc]; exact hh
  · rw [if_neg hc] at hh; rw [if_neg hc]; exact hh

theorem n178 (b x : Nat) :
    cuTripleWithin 2 0 178 197
      ((((CodeReq.singleton 178 (.lddw .r0 73014444032)).union (CodeReq.singleton 179 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 73014444032) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 73014444032 b 178 (by decide)
  sl_block_iter [h0, ja_spec 197 179]

theorem n196 (b x : Nat) :
    cuTripleWithin 1 0 196 197
      (((CodeReq.singleton 196 (.lddw .r0 81604378624))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 81604378624) ** (.r1 ↦ᵣ x)) := by
  exact cuTripleWithin_frame_right (.r1 ↦ᵣ x) (pcFree_regIs _ _)
    (lddw_spec .r0 81604378624 b 196 (by decide))

theorem n157 (b x : Nat) :
    cuTripleWithin 2 0 157 197
      ((((CodeReq.singleton 157 (.lddw .r0 77309411328)).union (CodeReq.singleton 158 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 77309411328) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 77309411328 b 157 (by decide)
  sl_block_iter [h0, ja_spec 197 158]

theorem n156 (b x : Nat) :
    cuTripleWithin 3 0 156 197
      (((((CodeReq.singleton 156 (.jne .r1 (.imm 17) 196))).union ((CodeReq.singleton 196 (.lddw .r0 81604378624)))).union (((CodeReq.singleton 157 (.lddw .r0 77309411328)).union (CodeReq.singleton 158 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 17 then toU64 81604378624 else toU64 77309411328)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 17 x 156 196)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n196 b x) (n157 b x))

theorem n155 (b x : Nat) :
    cuTripleWithin 4 0 155 197
      (((((CodeReq.singleton 155 (.jeq .r1 (.imm 16) 178))).union (((CodeReq.singleton 178 (.lddw .r0 73014444032)).union (CodeReq.singleton 179 (.ja 197))))).union ((((CodeReq.singleton 156 (.jne .r1 (.imm 17) 196))).union ((CodeReq.singleton 196 (.lddw .r0 81604378624)))).union (((CodeReq.singleton 157 (.lddw .r0 77309411328)).union (CodeReq.singleton 158 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x = toU64 16 then toU64 73014444032 else (if x ≠ toU64 17 then toU64 81604378624 else toU64 77309411328))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jeq_imm_branch_spec .r1 16 x 155 178)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n178 b x) (n156 b x))

theorem n174 (b x : Nat) :
    cuTripleWithin 2 0 174 197
      ((((CodeReq.singleton 174 (.lddw .r0 60129542144)).union (CodeReq.singleton 175 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 60129542144) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 60129542144 b 174 (by decide)
  sl_block_iter [h0, ja_spec 197 175]

theorem n192 (b x : Nat) :
    cuTripleWithin 2 0 192 197
      ((((CodeReq.singleton 192 (.lddw .r0 68719476736)).union (CodeReq.singleton 193 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 68719476736) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 68719476736 b 192 (by decide)
  sl_block_iter [h0, ja_spec 197 193]

theorem n141 (b x : Nat) :
    cuTripleWithin 2 0 141 197
      ((((CodeReq.singleton 141 (.lddw .r0 64424509440)).union (CodeReq.singleton 142 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 64424509440) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 64424509440 b 141 (by decide)
  sl_block_iter [h0, ja_spec 197 142]

theorem n140 (b x : Nat) :
    cuTripleWithin 3 0 140 197
      (((((CodeReq.singleton 140 (.jne .r1 (.imm 14) 192))).union (((CodeReq.singleton 192 (.lddw .r0 68719476736)).union (CodeReq.singleton 193 (.ja 197))))).union (((CodeReq.singleton 141 (.lddw .r0 64424509440)).union (CodeReq.singleton 142 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 14 then toU64 68719476736 else toU64 64424509440)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 14 x 140 192)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n192 b x) (n141 b x))

theorem n139 (b x : Nat) :
    cuTripleWithin 4 0 139 197
      (((((CodeReq.singleton 139 (.jeq .r1 (.imm 13) 174))).union (((CodeReq.singleton 174 (.lddw .r0 60129542144)).union (CodeReq.singleton 175 (.ja 197))))).union ((((CodeReq.singleton 140 (.jne .r1 (.imm 14) 192))).union (((CodeReq.singleton 192 (.lddw .r0 68719476736)).union (CodeReq.singleton 193 (.ja 197))))).union (((CodeReq.singleton 141 (.lddw .r0 64424509440)).union (CodeReq.singleton 142 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x = toU64 13 then toU64 60129542144 else (if x ≠ toU64 14 then toU64 68719476736 else toU64 64424509440))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jeq_imm_branch_spec .r1 13 x 139 174)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n174 b x) (n140 b x))

theorem n138 (b x : Nat) :
    cuTripleWithin 5 0 138 197
      (((((CodeReq.singleton 138 (.jsgt .r1 (.imm 15) 155))).union ((((CodeReq.singleton 155 (.jeq .r1 (.imm 16) 178))).union (((CodeReq.singleton 178 (.lddw .r0 73014444032)).union (CodeReq.singleton 179 (.ja 197))))).union ((((CodeReq.singleton 156 (.jne .r1 (.imm 17) 196))).union ((CodeReq.singleton 196 (.lddw .r0 81604378624)))).union (((CodeReq.singleton 157 (.lddw .r0 77309411328)).union (CodeReq.singleton 158 (.ja 197))))))).union ((((CodeReq.singleton 139 (.jeq .r1 (.imm 13) 174))).union (((CodeReq.singleton 174 (.lddw .r0 60129542144)).union (CodeReq.singleton 175 (.ja 197))))).union ((((CodeReq.singleton 140 (.jne .r1 (.imm 14) 192))).union (((CodeReq.singleton 192 (.lddw .r0 68719476736)).union (CodeReq.singleton 193 (.ja 197))))).union (((CodeReq.singleton 141 (.lddw .r0 64424509440)).union (CodeReq.singleton 142 (.ja 197))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x > toSigned64 (toU64 15) then (if x = toU64 16 then toU64 73014444032 else (if x ≠ toU64 17 then toU64 81604378624 else toU64 77309411328)) else (if x = toU64 13 then toU64 60129542144 else (if x ≠ toU64 14 then toU64 68719476736 else toU64 64424509440)))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsgt_imm_spec .r1 15 x 138 155).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n155 b x) (n139 b x))

theorem n167 (b x : Nat) :
    cuTripleWithin 2 0 167 197
      ((((CodeReq.singleton 167 (.lddw .r0 85899345920)).union (CodeReq.singleton 168 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 85899345920) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 85899345920 b 167 (by decide)
  sl_block_iter [h0, ja_spec 197 168]

theorem n182 (b x : Nat) :
    cuTripleWithin 2 0 182 197
      ((((CodeReq.singleton 182 (.lddw .r0 94489280512)).union (CodeReq.singleton 183 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 94489280512) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 94489280512 b 182 (by decide)
  sl_block_iter [h0, ja_spec 197 183]

theorem n149 (b x : Nat) :
    cuTripleWithin 2 0 149 197
      ((((CodeReq.singleton 149 (.lddw .r0 90194313216)).union (CodeReq.singleton 150 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 90194313216) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 90194313216 b 149 (by decide)
  sl_block_iter [h0, ja_spec 197 150]

theorem n148 (b x : Nat) :
    cuTripleWithin 3 0 148 197
      (((((CodeReq.singleton 148 (.jne .r1 (.imm 20) 182))).union (((CodeReq.singleton 182 (.lddw .r0 94489280512)).union (CodeReq.singleton 183 (.ja 197))))).union (((CodeReq.singleton 149 (.lddw .r0 90194313216)).union (CodeReq.singleton 150 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 20 then toU64 94489280512 else toU64 90194313216)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 20 x 148 182)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n182 b x) (n149 b x))

theorem n147 (b x : Nat) :
    cuTripleWithin 4 0 147 197
      (((((CodeReq.singleton 147 (.jeq .r1 (.imm 19) 167))).union (((CodeReq.singleton 167 (.lddw .r0 85899345920)).union (CodeReq.singleton 168 (.ja 197))))).union ((((CodeReq.singleton 148 (.jne .r1 (.imm 20) 182))).union (((CodeReq.singleton 182 (.lddw .r0 94489280512)).union (CodeReq.singleton 183 (.ja 197))))).union (((CodeReq.singleton 149 (.lddw .r0 90194313216)).union (CodeReq.singleton 150 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x = toU64 19 then toU64 85899345920 else (if x ≠ toU64 20 then toU64 94489280512 else toU64 90194313216))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jeq_imm_branch_spec .r1 19 x 147 167)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n167 b x) (n148 b x))

theorem n190 (b x : Nat) :
    cuTripleWithin 2 0 190 197
      ((((CodeReq.singleton 190 (.lddw .r0 111669149696)).union (CodeReq.singleton 191 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 111669149696) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 111669149696 b 190 (by decide)
  sl_block_iter [h0, ja_spec 197 191]

theorem n163 (b x : Nat) :
    cuTripleWithin 2 0 163 197
      ((((CodeReq.singleton 163 (.lddw .r0 107374182400)).union (CodeReq.singleton 164 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 107374182400) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 107374182400 b 163 (by decide)
  sl_block_iter [h0, ja_spec 197 164]

theorem n162 (b x : Nat) :
    cuTripleWithin 3 0 162 197
      (((((CodeReq.singleton 162 (.jne .r1 (.imm 24) 190))).union (((CodeReq.singleton 190 (.lddw .r0 111669149696)).union (CodeReq.singleton 191 (.ja 197))))).union (((CodeReq.singleton 163 (.lddw .r0 107374182400)).union (CodeReq.singleton 164 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 24 then toU64 111669149696 else toU64 107374182400)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 24 x 162 190)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n190 b x) (n163 b x))

theorem n186 (b x : Nat) :
    cuTripleWithin 2 0 186 197
      ((((CodeReq.singleton 186 (.lddw .r0 103079215104)).union (CodeReq.singleton 187 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 103079215104) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 103079215104 b 186 (by decide)
  sl_block_iter [h0, ja_spec 197 187]

theorem n130 (b x : Nat) :
    cuTripleWithin 2 0 130 197
      ((((CodeReq.singleton 130 (.lddw .r0 98784247808)).union (CodeReq.singleton 131 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 98784247808) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 98784247808 b 130 (by decide)
  sl_block_iter [h0, ja_spec 197 131]

theorem n129 (b x : Nat) :
    cuTripleWithin 3 0 129 197
      (((((CodeReq.singleton 129 (.jne .r1 (.imm 22) 186))).union (((CodeReq.singleton 186 (.lddw .r0 103079215104)).union (CodeReq.singleton 187 (.ja 197))))).union (((CodeReq.singleton 130 (.lddw .r0 98784247808)).union (CodeReq.singleton 131 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 22 then toU64 103079215104 else toU64 98784247808)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 22 x 129 186)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n186 b x) (n130 b x))

theorem n128 (b x : Nat) :
    cuTripleWithin 4 0 128 197
      (((((CodeReq.singleton 128 (.jsgt .r1 (.imm 23) 162))).union ((((CodeReq.singleton 162 (.jne .r1 (.imm 24) 190))).union (((CodeReq.singleton 190 (.lddw .r0 111669149696)).union (CodeReq.singleton 191 (.ja 197))))).union (((CodeReq.singleton 163 (.lddw .r0 107374182400)).union (CodeReq.singleton 164 (.ja 197)))))).union ((((CodeReq.singleton 129 (.jne .r1 (.imm 22) 186))).union (((CodeReq.singleton 186 (.lddw .r0 103079215104)).union (CodeReq.singleton 187 (.ja 197))))).union (((CodeReq.singleton 130 (.lddw .r0 98784247808)).union (CodeReq.singleton 131 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x > toSigned64 (toU64 23) then (if x ≠ toU64 24 then toU64 111669149696 else toU64 107374182400) else (if x ≠ toU64 22 then toU64 103079215104 else toU64 98784247808))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsgt_imm_spec .r1 23 x 128 162).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n162 b x) (n129 b x))

theorem n127 (b x : Nat) :
    cuTripleWithin 5 0 127 197
      (((((CodeReq.singleton 127 (.jsle .r1 (.imm 21) 147))).union ((((CodeReq.singleton 147 (.jeq .r1 (.imm 19) 167))).union (((CodeReq.singleton 167 (.lddw .r0 85899345920)).union (CodeReq.singleton 168 (.ja 197))))).union ((((CodeReq.singleton 148 (.jne .r1 (.imm 20) 182))).union (((CodeReq.singleton 182 (.lddw .r0 94489280512)).union (CodeReq.singleton 183 (.ja 197))))).union (((CodeReq.singleton 149 (.lddw .r0 90194313216)).union (CodeReq.singleton 150 (.ja 197))))))).union ((((CodeReq.singleton 128 (.jsgt .r1 (.imm 23) 162))).union ((((CodeReq.singleton 162 (.jne .r1 (.imm 24) 190))).union (((CodeReq.singleton 190 (.lddw .r0 111669149696)).union (CodeReq.singleton 191 (.ja 197))))).union (((CodeReq.singleton 163 (.lddw .r0 107374182400)).union (CodeReq.singleton 164 (.ja 197)))))).union ((((CodeReq.singleton 129 (.jne .r1 (.imm 22) 186))).union (((CodeReq.singleton 186 (.lddw .r0 103079215104)).union (CodeReq.singleton 187 (.ja 197))))).union (((CodeReq.singleton 130 (.lddw .r0 98784247808)).union (CodeReq.singleton 131 (.ja 197))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x ≤ toSigned64 (toU64 21) then (if x = toU64 19 then toU64 85899345920 else (if x ≠ toU64 20 then toU64 94489280512 else toU64 90194313216)) else (if toSigned64 x > toSigned64 (toU64 23) then (if x ≠ toU64 24 then toU64 111669149696 else toU64 107374182400) else (if x ≠ toU64 22 then toU64 103079215104 else toU64 98784247808)))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsle_imm_spec .r1 21 x 127 147).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n147 b x) (n128 b x))

theorem n126 (b x : Nat) :
    cuTripleWithin 6 0 126 197
      (((((CodeReq.singleton 126 (.jsle .r1 (.imm 18) 138))).union ((((CodeReq.singleton 138 (.jsgt .r1 (.imm 15) 155))).union ((((CodeReq.singleton 155 (.jeq .r1 (.imm 16) 178))).union (((CodeReq.singleton 178 (.lddw .r0 73014444032)).union (CodeReq.singleton 179 (.ja 197))))).union ((((CodeReq.singleton 156 (.jne .r1 (.imm 17) 196))).union ((CodeReq.singleton 196 (.lddw .r0 81604378624)))).union (((CodeReq.singleton 157 (.lddw .r0 77309411328)).union (CodeReq.singleton 158 (.ja 197))))))).union ((((CodeReq.singleton 139 (.jeq .r1 (.imm 13) 174))).union (((CodeReq.singleton 174 (.lddw .r0 60129542144)).union (CodeReq.singleton 175 (.ja 197))))).union ((((CodeReq.singleton 140 (.jne .r1 (.imm 14) 192))).union (((CodeReq.singleton 192 (.lddw .r0 68719476736)).union (CodeReq.singleton 193 (.ja 197))))).union (((CodeReq.singleton 141 (.lddw .r0 64424509440)).union (CodeReq.singleton 142 (.ja 197)))))))).union ((((CodeReq.singleton 127 (.jsle .r1 (.imm 21) 147))).union ((((CodeReq.singleton 147 (.jeq .r1 (.imm 19) 167))).union (((CodeReq.singleton 167 (.lddw .r0 85899345920)).union (CodeReq.singleton 168 (.ja 197))))).union ((((CodeReq.singleton 148 (.jne .r1 (.imm 20) 182))).union (((CodeReq.singleton 182 (.lddw .r0 94489280512)).union (CodeReq.singleton 183 (.ja 197))))).union (((CodeReq.singleton 149 (.lddw .r0 90194313216)).union (CodeReq.singleton 150 (.ja 197))))))).union ((((CodeReq.singleton 128 (.jsgt .r1 (.imm 23) 162))).union ((((CodeReq.singleton 162 (.jne .r1 (.imm 24) 190))).union (((CodeReq.singleton 190 (.lddw .r0 111669149696)).union (CodeReq.singleton 191 (.ja 197))))).union (((CodeReq.singleton 163 (.lddw .r0 107374182400)).union (CodeReq.singleton 164 (.ja 197)))))).union ((((CodeReq.singleton 129 (.jne .r1 (.imm 22) 186))).union (((CodeReq.singleton 186 (.lddw .r0 103079215104)).union (CodeReq.singleton 187 (.ja 197))))).union (((CodeReq.singleton 130 (.lddw .r0 98784247808)).union (CodeReq.singleton 131 (.ja 197)))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x ≤ toSigned64 (toU64 18) then (if toSigned64 x > toSigned64 (toU64 15) then (if x = toU64 16 then toU64 73014444032 else (if x ≠ toU64 17 then toU64 81604378624 else toU64 77309411328)) else (if x = toU64 13 then toU64 60129542144 else (if x ≠ toU64 14 then toU64 68719476736 else toU64 64424509440))) else (if toSigned64 x ≤ toSigned64 (toU64 21) then (if x = toU64 19 then toU64 85899345920 else (if x ≠ toU64 20 then toU64 94489280512 else toU64 90194313216)) else (if toSigned64 x > toSigned64 (toU64 23) then (if x ≠ toU64 24 then toU64 111669149696 else toU64 107374182400) else (if x ≠ toU64 22 then toU64 103079215104 else toU64 98784247808))))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsle_imm_spec .r1 18 x 126 138).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n138 b x) (n127 b x))

theorem n176 (b x : Nat) :
    cuTripleWithin 2 0 176 197
      ((((CodeReq.singleton 176 (.lddw .r0 17179869184)).union (CodeReq.singleton 177 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 17179869184) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 17179869184 b 176 (by decide)
  sl_block_iter [h0, ja_spec 197 177]

theorem n194 (b x : Nat) :
    cuTripleWithin 2 0 194 197
      ((((CodeReq.singleton 194 (.lddw .r0 25769803776)).union (CodeReq.singleton 195 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 25769803776) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 25769803776 b 194 (by decide)
  sl_block_iter [h0, ja_spec 197 195]

theorem n153 (b x : Nat) :
    cuTripleWithin 2 0 153 197
      ((((CodeReq.singleton 153 (.lddw .r0 21474836480)).union (CodeReq.singleton 154 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 21474836480) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 21474836480 b 153 (by decide)
  sl_block_iter [h0, ja_spec 197 154]

theorem n152 (b x : Nat) :
    cuTripleWithin 3 0 152 197
      (((((CodeReq.singleton 152 (.jne .r1 (.imm 4) 194))).union (((CodeReq.singleton 194 (.lddw .r0 25769803776)).union (CodeReq.singleton 195 (.ja 197))))).union (((CodeReq.singleton 153 (.lddw .r0 21474836480)).union (CodeReq.singleton 154 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 4 then toU64 25769803776 else toU64 21474836480)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 4 x 152 194)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n194 b x) (n153 b x))

theorem n151 (b x : Nat) :
    cuTripleWithin 4 0 151 197
      (((((CodeReq.singleton 151 (.jeq .r1 (.imm 3) 176))).union (((CodeReq.singleton 176 (.lddw .r0 17179869184)).union (CodeReq.singleton 177 (.ja 197))))).union ((((CodeReq.singleton 152 (.jne .r1 (.imm 4) 194))).union (((CodeReq.singleton 194 (.lddw .r0 25769803776)).union (CodeReq.singleton 195 (.ja 197))))).union (((CodeReq.singleton 153 (.lddw .r0 21474836480)).union (CodeReq.singleton 154 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x = toU64 3 then toU64 17179869184 else (if x ≠ toU64 4 then toU64 25769803776 else toU64 21474836480))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jeq_imm_branch_spec .r1 3 x 151 176)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n176 b x) (n152 b x))

theorem n172 (b x : Nat) :
    cuTripleWithin 2 0 172 197
      ((((CodeReq.singleton 172 (.lddw .r0 4294967296)).union (CodeReq.singleton 173 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 4294967296) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 4294967296 b 172 (by decide)
  sl_block_iter [h0, ja_spec 197 173]

theorem n169 (b x : Nat) :
    cuTripleWithin 5 0 169 197
      (((((CodeReq.singleton 169 (.lsh64 .r0 (.imm 32)))).union (CodeReq.singleton 170 (.rsh64 .r0 (.imm 32)))).union ((((CodeReq.singleton 171 (.jne .r0 (.imm 0) 197))).union CodeReq.empty).union (((CodeReq.singleton 172 (.lddw .r0 4294967296)).union (CodeReq.singleton 173 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≠ toU64 0 then (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) else toU64 4294967296)) ** (.r1 ↦ᵣ x)) := by
  have h0 := lsh64_imm_spec .r0 32 b 169 (by decide)
  have h1 := rsh64_imm_spec .r0 32 ((b <<< (toU64 32 % 64)) % U64_MODULUS) 170 (by decide)
  have h01 := cuTripleWithin_frame_right (.r1 ↦ᵣ x) (pcFree_regIs _ _)
    (cuTripleWithin_seq (by sl_disjoint_codereq) h0 h1)
  have h_br := cuTripleWithinBranch_frame_right (.r1 ↦ᵣ x) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r0 0 (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) 171 197)
  have hj := cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (cuTripleWithin_refl (fun _ h => h)) (n172 (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) x))
  exact cuTripleWithin_seq (by sl_disjoint_codereq) h01 hj

theorem n136 (b x : Nat) :
    cuTripleWithin 2 0 136 197
      ((((CodeReq.singleton 136 (.lddw .r0 12884901888)).union (CodeReq.singleton 137 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 12884901888) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 12884901888 b 136 (by decide)
  sl_block_iter [h0, ja_spec 197 137]

theorem n134 (b x : Nat) :
    cuTripleWithin 4 0 134 197
      ((((CodeReq.singleton 134 (.lddw .r0 8589934592))).union ((((CodeReq.singleton 135 (.jeq .r1 (.imm 1) 197))).union CodeReq.empty).union (((CodeReq.singleton 136 (.lddw .r0 12884901888)).union (CodeReq.singleton 137 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x = toU64 1 then toU64 8589934592 else toU64 12884901888)) ** (.r1 ↦ᵣ x)) := by
  have h0 := cuTripleWithin_frame_right (.r1 ↦ᵣ x) (pcFree_regIs _ _)
    (lddw_spec .r0 8589934592 b 134 (by decide))
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ toU64 8589934592) (pcFree_regIs _ _)
    (jeq_imm_branch_spec .r1 1 x 135 197)
  have hj := cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (cuTripleWithin_refl (fun _ h => h)) (n136 (toU64 8589934592) x))
  exact cuTripleWithin_seq (by sl_disjoint_codereq) h0 hj

theorem n133 (b x : Nat) :
    cuTripleWithin 6 0 133 197
      (((((CodeReq.singleton 133 (.jeq .r1 (.imm 0) 169))).union ((((CodeReq.singleton 169 (.lsh64 .r0 (.imm 32)))).union (CodeReq.singleton 170 (.rsh64 .r0 (.imm 32)))).union ((((CodeReq.singleton 171 (.jne .r0 (.imm 0) 197))).union CodeReq.empty).union (((CodeReq.singleton 172 (.lddw .r0 4294967296)).union (CodeReq.singleton 173 (.ja 197))))))).union (((CodeReq.singleton 134 (.lddw .r0 8589934592))).union ((((CodeReq.singleton 135 (.jeq .r1 (.imm 1) 197))).union CodeReq.empty).union (((CodeReq.singleton 136 (.lddw .r0 12884901888)).union (CodeReq.singleton 137 (.ja 197))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x = toU64 0 then (if (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≠ toU64 0 then (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) else toU64 4294967296) else (if x = toU64 1 then toU64 8589934592 else toU64 12884901888))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jeq_imm_branch_spec .r1 0 x 133 169)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n169 b x) (n134 b x))

theorem n132 (b x : Nat) :
    cuTripleWithin 7 0 132 197
      (((((CodeReq.singleton 132 (.jsgt .r1 (.imm 2) 151))).union ((((CodeReq.singleton 151 (.jeq .r1 (.imm 3) 176))).union (((CodeReq.singleton 176 (.lddw .r0 17179869184)).union (CodeReq.singleton 177 (.ja 197))))).union ((((CodeReq.singleton 152 (.jne .r1 (.imm 4) 194))).union (((CodeReq.singleton 194 (.lddw .r0 25769803776)).union (CodeReq.singleton 195 (.ja 197))))).union (((CodeReq.singleton 153 (.lddw .r0 21474836480)).union (CodeReq.singleton 154 (.ja 197))))))).union ((((CodeReq.singleton 133 (.jeq .r1 (.imm 0) 169))).union ((((CodeReq.singleton 169 (.lsh64 .r0 (.imm 32)))).union (CodeReq.singleton 170 (.rsh64 .r0 (.imm 32)))).union ((((CodeReq.singleton 171 (.jne .r0 (.imm 0) 197))).union CodeReq.empty).union (((CodeReq.singleton 172 (.lddw .r0 4294967296)).union (CodeReq.singleton 173 (.ja 197))))))).union (((CodeReq.singleton 134 (.lddw .r0 8589934592))).union ((((CodeReq.singleton 135 (.jeq .r1 (.imm 1) 197))).union CodeReq.empty).union (((CodeReq.singleton 136 (.lddw .r0 12884901888)).union (CodeReq.singleton 137 (.ja 197)))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x > toSigned64 (toU64 2) then (if x = toU64 3 then toU64 17179869184 else (if x ≠ toU64 4 then toU64 25769803776 else toU64 21474836480)) else (if x = toU64 0 then (if (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≠ toU64 0 then (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) else toU64 4294967296) else (if x = toU64 1 then toU64 8589934592 else toU64 12884901888)))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsgt_imm_spec .r1 2 x 132 151).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n151 b x) (n133 b x))

theorem n165 (b x : Nat) :
    cuTripleWithin 2 0 165 197
      ((((CodeReq.singleton 165 (.lddw .r0 30064771072)).union (CodeReq.singleton 166 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 30064771072) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 30064771072 b 165 (by decide)
  sl_block_iter [h0, ja_spec 197 166]

theorem n180 (b x : Nat) :
    cuTripleWithin 2 0 180 197
      ((((CodeReq.singleton 180 (.lddw .r0 38654705664)).union (CodeReq.singleton 181 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 38654705664) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 38654705664 b 180 (by decide)
  sl_block_iter [h0, ja_spec 197 181]

theorem n145 (b x : Nat) :
    cuTripleWithin 2 0 145 197
      ((((CodeReq.singleton 145 (.lddw .r0 34359738368)).union (CodeReq.singleton 146 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 34359738368) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 34359738368 b 145 (by decide)
  sl_block_iter [h0, ja_spec 197 146]

theorem n144 (b x : Nat) :
    cuTripleWithin 3 0 144 197
      (((((CodeReq.singleton 144 (.jne .r1 (.imm 7) 180))).union (((CodeReq.singleton 180 (.lddw .r0 38654705664)).union (CodeReq.singleton 181 (.ja 197))))).union (((CodeReq.singleton 145 (.lddw .r0 34359738368)).union (CodeReq.singleton 146 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 7 then toU64 38654705664 else toU64 34359738368)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 7 x 144 180)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n180 b x) (n145 b x))

theorem n143 (b x : Nat) :
    cuTripleWithin 4 0 143 197
      (((((CodeReq.singleton 143 (.jeq .r1 (.imm 6) 165))).union (((CodeReq.singleton 165 (.lddw .r0 30064771072)).union (CodeReq.singleton 166 (.ja 197))))).union ((((CodeReq.singleton 144 (.jne .r1 (.imm 7) 180))).union (((CodeReq.singleton 180 (.lddw .r0 38654705664)).union (CodeReq.singleton 181 (.ja 197))))).union (((CodeReq.singleton 145 (.lddw .r0 34359738368)).union (CodeReq.singleton 146 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x = toU64 6 then toU64 30064771072 else (if x ≠ toU64 7 then toU64 38654705664 else toU64 34359738368))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jeq_imm_branch_spec .r1 6 x 143 165)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n165 b x) (n144 b x))

theorem n188 (b x : Nat) :
    cuTripleWithin 2 0 188 197
      ((((CodeReq.singleton 188 (.lddw .r0 55834574848)).union (CodeReq.singleton 189 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 55834574848) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 55834574848 b 188 (by decide)
  sl_block_iter [h0, ja_spec 197 189]

theorem n160 (b x : Nat) :
    cuTripleWithin 2 0 160 197
      ((((CodeReq.singleton 160 (.lddw .r0 51539607552)).union (CodeReq.singleton 161 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 51539607552) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 51539607552 b 160 (by decide)
  sl_block_iter [h0, ja_spec 197 161]

theorem n159 (b x : Nat) :
    cuTripleWithin 3 0 159 197
      (((((CodeReq.singleton 159 (.jne .r1 (.imm 11) 188))).union (((CodeReq.singleton 188 (.lddw .r0 55834574848)).union (CodeReq.singleton 189 (.ja 197))))).union (((CodeReq.singleton 160 (.lddw .r0 51539607552)).union (CodeReq.singleton 161 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 11 then toU64 55834574848 else toU64 51539607552)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 11 x 159 188)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n188 b x) (n160 b x))

theorem n184 (b x : Nat) :
    cuTripleWithin 2 0 184 197
      ((((CodeReq.singleton 184 (.lddw .r0 47244640256)).union (CodeReq.singleton 185 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 47244640256) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 47244640256 b 184 (by decide)
  sl_block_iter [h0, ja_spec 197 185]

theorem n124 (b x : Nat) :
    cuTripleWithin 2 0 124 197
      ((((CodeReq.singleton 124 (.lddw .r0 42949672960)).union (CodeReq.singleton 125 (.ja 197)))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ toU64 42949672960) ** (.r1 ↦ᵣ x)) := by
  have h0 := lddw_spec .r0 42949672960 b 124 (by decide)
  sl_block_iter [h0, ja_spec 197 125]

theorem n123 (b x : Nat) :
    cuTripleWithin 3 0 123 197
      (((((CodeReq.singleton 123 (.jne .r1 (.imm 9) 184))).union (((CodeReq.singleton 184 (.lddw .r0 47244640256)).union (CodeReq.singleton 185 (.ja 197))))).union (((CodeReq.singleton 124 (.lddw .r0 42949672960)).union (CodeReq.singleton 125 (.ja 197))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if x ≠ toU64 9 then toU64 47244640256 else toU64 42949672960)) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jne_imm_branch_spec .r1 9 x 123 184)
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n184 b x) (n124 b x))

theorem n122 (b x : Nat) :
    cuTripleWithin 4 0 122 197
      (((((CodeReq.singleton 122 (.jsgt .r1 (.imm 10) 159))).union ((((CodeReq.singleton 159 (.jne .r1 (.imm 11) 188))).union (((CodeReq.singleton 188 (.lddw .r0 55834574848)).union (CodeReq.singleton 189 (.ja 197))))).union (((CodeReq.singleton 160 (.lddw .r0 51539607552)).union (CodeReq.singleton 161 (.ja 197)))))).union ((((CodeReq.singleton 123 (.jne .r1 (.imm 9) 184))).union (((CodeReq.singleton 184 (.lddw .r0 47244640256)).union (CodeReq.singleton 185 (.ja 197))))).union (((CodeReq.singleton 124 (.lddw .r0 42949672960)).union (CodeReq.singleton 125 (.ja 197)))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x > toSigned64 (toU64 10) then (if x ≠ toU64 11 then toU64 55834574848 else toU64 51539607552) else (if x ≠ toU64 9 then toU64 47244640256 else toU64 42949672960))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsgt_imm_spec .r1 10 x 122 159).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n159 b x) (n123 b x))

theorem n121 (b x : Nat) :
    cuTripleWithin 5 0 121 197
      (((((CodeReq.singleton 121 (.jsle .r1 (.imm 8) 143))).union ((((CodeReq.singleton 143 (.jeq .r1 (.imm 6) 165))).union (((CodeReq.singleton 165 (.lddw .r0 30064771072)).union (CodeReq.singleton 166 (.ja 197))))).union ((((CodeReq.singleton 144 (.jne .r1 (.imm 7) 180))).union (((CodeReq.singleton 180 (.lddw .r0 38654705664)).union (CodeReq.singleton 181 (.ja 197))))).union (((CodeReq.singleton 145 (.lddw .r0 34359738368)).union (CodeReq.singleton 146 (.ja 197))))))).union ((((CodeReq.singleton 122 (.jsgt .r1 (.imm 10) 159))).union ((((CodeReq.singleton 159 (.jne .r1 (.imm 11) 188))).union (((CodeReq.singleton 188 (.lddw .r0 55834574848)).union (CodeReq.singleton 189 (.ja 197))))).union (((CodeReq.singleton 160 (.lddw .r0 51539607552)).union (CodeReq.singleton 161 (.ja 197)))))).union ((((CodeReq.singleton 123 (.jne .r1 (.imm 9) 184))).union (((CodeReq.singleton 184 (.lddw .r0 47244640256)).union (CodeReq.singleton 185 (.ja 197))))).union (((CodeReq.singleton 124 (.lddw .r0 42949672960)).union (CodeReq.singleton 125 (.ja 197))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x ≤ toSigned64 (toU64 8) then (if x = toU64 6 then toU64 30064771072 else (if x ≠ toU64 7 then toU64 38654705664 else toU64 34359738368)) else (if toSigned64 x > toSigned64 (toU64 10) then (if x ≠ toU64 11 then toU64 55834574848 else toU64 51539607552) else (if x ≠ toU64 9 then toU64 47244640256 else toU64 42949672960)))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsle_imm_spec .r1 8 x 121 143).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n143 b x) (n122 b x))

set_option maxHeartbeats 1000000 in
theorem n120 (b x : Nat) :
    cuTripleWithin 8 0 120 197
      (((((CodeReq.singleton 120 (.jsle .r1 (.imm 5) 132))).union ((((CodeReq.singleton 132 (.jsgt .r1 (.imm 2) 151))).union ((((CodeReq.singleton 151 (.jeq .r1 (.imm 3) 176))).union (((CodeReq.singleton 176 (.lddw .r0 17179869184)).union (CodeReq.singleton 177 (.ja 197))))).union ((((CodeReq.singleton 152 (.jne .r1 (.imm 4) 194))).union (((CodeReq.singleton 194 (.lddw .r0 25769803776)).union (CodeReq.singleton 195 (.ja 197))))).union (((CodeReq.singleton 153 (.lddw .r0 21474836480)).union (CodeReq.singleton 154 (.ja 197))))))).union ((((CodeReq.singleton 133 (.jeq .r1 (.imm 0) 169))).union ((((CodeReq.singleton 169 (.lsh64 .r0 (.imm 32)))).union (CodeReq.singleton 170 (.rsh64 .r0 (.imm 32)))).union ((((CodeReq.singleton 171 (.jne .r0 (.imm 0) 197))).union CodeReq.empty).union (((CodeReq.singleton 172 (.lddw .r0 4294967296)).union (CodeReq.singleton 173 (.ja 197))))))).union (((CodeReq.singleton 134 (.lddw .r0 8589934592))).union ((((CodeReq.singleton 135 (.jeq .r1 (.imm 1) 197))).union CodeReq.empty).union (((CodeReq.singleton 136 (.lddw .r0 12884901888)).union (CodeReq.singleton 137 (.ja 197))))))))).union ((((CodeReq.singleton 121 (.jsle .r1 (.imm 8) 143))).union ((((CodeReq.singleton 143 (.jeq .r1 (.imm 6) 165))).union (((CodeReq.singleton 165 (.lddw .r0 30064771072)).union (CodeReq.singleton 166 (.ja 197))))).union ((((CodeReq.singleton 144 (.jne .r1 (.imm 7) 180))).union (((CodeReq.singleton 180 (.lddw .r0 38654705664)).union (CodeReq.singleton 181 (.ja 197))))).union (((CodeReq.singleton 145 (.lddw .r0 34359738368)).union (CodeReq.singleton 146 (.ja 197))))))).union ((((CodeReq.singleton 122 (.jsgt .r1 (.imm 10) 159))).union ((((CodeReq.singleton 159 (.jne .r1 (.imm 11) 188))).union (((CodeReq.singleton 188 (.lddw .r0 55834574848)).union (CodeReq.singleton 189 (.ja 197))))).union (((CodeReq.singleton 160 (.lddw .r0 51539607552)).union (CodeReq.singleton 161 (.ja 197)))))).union ((((CodeReq.singleton 123 (.jne .r1 (.imm 9) 184))).union (((CodeReq.singleton 184 (.lddw .r0 47244640256)).union (CodeReq.singleton 185 (.ja 197))))).union (((CodeReq.singleton 124 (.lddw .r0 42949672960)).union (CodeReq.singleton 125 (.ja 197)))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x ≤ toSigned64 (toU64 5) then (if toSigned64 x > toSigned64 (toU64 2) then (if x = toU64 3 then toU64 17179869184 else (if x ≠ toU64 4 then toU64 25769803776 else toU64 21474836480)) else (if x = toU64 0 then (if (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≠ toU64 0 then (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) else toU64 4294967296) else (if x = toU64 1 then toU64 8589934592 else toU64 12884901888))) else (if toSigned64 x ≤ toSigned64 (toU64 8) then (if x = toU64 6 then toU64 30064771072 else (if x ≠ toU64 7 then toU64 38654705664 else toU64 34359738368)) else (if toSigned64 x > toSigned64 (toU64 10) then (if x ≠ toU64 11 then toU64 55834574848 else toU64 51539607552) else (if x ≠ toU64 9 then toU64 47244640256 else toU64 42949672960))))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsle_imm_spec .r1 5 x 120 132).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n132 b x) (n121 b x))

set_option maxHeartbeats 1000000 in
theorem n119 (b x : Nat) :
    cuTripleWithin 9 0 119 197
      (((((CodeReq.singleton 119 (.jsgt .r1 (.imm 12) 126))).union ((((CodeReq.singleton 126 (.jsle .r1 (.imm 18) 138))).union ((((CodeReq.singleton 138 (.jsgt .r1 (.imm 15) 155))).union ((((CodeReq.singleton 155 (.jeq .r1 (.imm 16) 178))).union (((CodeReq.singleton 178 (.lddw .r0 73014444032)).union (CodeReq.singleton 179 (.ja 197))))).union ((((CodeReq.singleton 156 (.jne .r1 (.imm 17) 196))).union ((CodeReq.singleton 196 (.lddw .r0 81604378624)))).union (((CodeReq.singleton 157 (.lddw .r0 77309411328)).union (CodeReq.singleton 158 (.ja 197))))))).union ((((CodeReq.singleton 139 (.jeq .r1 (.imm 13) 174))).union (((CodeReq.singleton 174 (.lddw .r0 60129542144)).union (CodeReq.singleton 175 (.ja 197))))).union ((((CodeReq.singleton 140 (.jne .r1 (.imm 14) 192))).union (((CodeReq.singleton 192 (.lddw .r0 68719476736)).union (CodeReq.singleton 193 (.ja 197))))).union (((CodeReq.singleton 141 (.lddw .r0 64424509440)).union (CodeReq.singleton 142 (.ja 197)))))))).union ((((CodeReq.singleton 127 (.jsle .r1 (.imm 21) 147))).union ((((CodeReq.singleton 147 (.jeq .r1 (.imm 19) 167))).union (((CodeReq.singleton 167 (.lddw .r0 85899345920)).union (CodeReq.singleton 168 (.ja 197))))).union ((((CodeReq.singleton 148 (.jne .r1 (.imm 20) 182))).union (((CodeReq.singleton 182 (.lddw .r0 94489280512)).union (CodeReq.singleton 183 (.ja 197))))).union (((CodeReq.singleton 149 (.lddw .r0 90194313216)).union (CodeReq.singleton 150 (.ja 197))))))).union ((((CodeReq.singleton 128 (.jsgt .r1 (.imm 23) 162))).union ((((CodeReq.singleton 162 (.jne .r1 (.imm 24) 190))).union (((CodeReq.singleton 190 (.lddw .r0 111669149696)).union (CodeReq.singleton 191 (.ja 197))))).union (((CodeReq.singleton 163 (.lddw .r0 107374182400)).union (CodeReq.singleton 164 (.ja 197)))))).union ((((CodeReq.singleton 129 (.jne .r1 (.imm 22) 186))).union (((CodeReq.singleton 186 (.lddw .r0 103079215104)).union (CodeReq.singleton 187 (.ja 197))))).union (((CodeReq.singleton 130 (.lddw .r0 98784247808)).union (CodeReq.singleton 131 (.ja 197))))))))).union ((((CodeReq.singleton 120 (.jsle .r1 (.imm 5) 132))).union ((((CodeReq.singleton 132 (.jsgt .r1 (.imm 2) 151))).union ((((CodeReq.singleton 151 (.jeq .r1 (.imm 3) 176))).union (((CodeReq.singleton 176 (.lddw .r0 17179869184)).union (CodeReq.singleton 177 (.ja 197))))).union ((((CodeReq.singleton 152 (.jne .r1 (.imm 4) 194))).union (((CodeReq.singleton 194 (.lddw .r0 25769803776)).union (CodeReq.singleton 195 (.ja 197))))).union (((CodeReq.singleton 153 (.lddw .r0 21474836480)).union (CodeReq.singleton 154 (.ja 197))))))).union ((((CodeReq.singleton 133 (.jeq .r1 (.imm 0) 169))).union ((((CodeReq.singleton 169 (.lsh64 .r0 (.imm 32)))).union (CodeReq.singleton 170 (.rsh64 .r0 (.imm 32)))).union ((((CodeReq.singleton 171 (.jne .r0 (.imm 0) 197))).union CodeReq.empty).union (((CodeReq.singleton 172 (.lddw .r0 4294967296)).union (CodeReq.singleton 173 (.ja 197))))))).union (((CodeReq.singleton 134 (.lddw .r0 8589934592))).union ((((CodeReq.singleton 135 (.jeq .r1 (.imm 1) 197))).union CodeReq.empty).union (((CodeReq.singleton 136 (.lddw .r0 12884901888)).union (CodeReq.singleton 137 (.ja 197))))))))).union ((((CodeReq.singleton 121 (.jsle .r1 (.imm 8) 143))).union ((((CodeReq.singleton 143 (.jeq .r1 (.imm 6) 165))).union (((CodeReq.singleton 165 (.lddw .r0 30064771072)).union (CodeReq.singleton 166 (.ja 197))))).union ((((CodeReq.singleton 144 (.jne .r1 (.imm 7) 180))).union (((CodeReq.singleton 180 (.lddw .r0 38654705664)).union (CodeReq.singleton 181 (.ja 197))))).union (((CodeReq.singleton 145 (.lddw .r0 34359738368)).union (CodeReq.singleton 146 (.ja 197))))))).union ((((CodeReq.singleton 122 (.jsgt .r1 (.imm 10) 159))).union ((((CodeReq.singleton 159 (.jne .r1 (.imm 11) 188))).union (((CodeReq.singleton 188 (.lddw .r0 55834574848)).union (CodeReq.singleton 189 (.ja 197))))).union (((CodeReq.singleton 160 (.lddw .r0 51539607552)).union (CodeReq.singleton 161 (.ja 197)))))).union ((((CodeReq.singleton 123 (.jne .r1 (.imm 9) 184))).union (((CodeReq.singleton 184 (.lddw .r0 47244640256)).union (CodeReq.singleton 185 (.ja 197))))).union (((CodeReq.singleton 124 (.lddw .r0 42949672960)).union (CodeReq.singleton 125 (.ja 197))))))))))
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x))
      ((.r0 ↦ᵣ (if toSigned64 x > toSigned64 (toU64 12) then (if toSigned64 x ≤ toSigned64 (toU64 18) then (if toSigned64 x > toSigned64 (toU64 15) then (if x = toU64 16 then toU64 73014444032 else (if x ≠ toU64 17 then toU64 81604378624 else toU64 77309411328)) else (if x = toU64 13 then toU64 60129542144 else (if x ≠ toU64 14 then toU64 68719476736 else toU64 64424509440))) else (if toSigned64 x ≤ toSigned64 (toU64 21) then (if x = toU64 19 then toU64 85899345920 else (if x ≠ toU64 20 then toU64 94489280512 else toU64 90194313216)) else (if toSigned64 x > toSigned64 (toU64 23) then (if x ≠ toU64 24 then toU64 111669149696 else toU64 107374182400) else (if x ≠ toU64 22 then toU64 103079215104 else toU64 98784247808)))) else (if toSigned64 x ≤ toSigned64 (toU64 5) then (if toSigned64 x > toSigned64 (toU64 2) then (if x = toU64 3 then toU64 17179869184 else (if x ≠ toU64 4 then toU64 25769803776 else toU64 21474836480)) else (if x = toU64 0 then (if (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≠ toU64 0 then (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) else toU64 4294967296) else (if x = toU64 1 then toU64 8589934592 else toU64 12884901888))) else (if toSigned64 x ≤ toSigned64 (toU64 8) then (if x = toU64 6 then toU64 30064771072 else (if x ≠ toU64 7 then toU64 38654705664 else toU64 34359738368)) else (if toSigned64 x > toSigned64 (toU64 10) then (if x ≠ toU64 11 then toU64 55834574848 else toU64 51539607552) else (if x ≠ toU64 9 then toU64 47244640256 else toU64 42949672960)))))) ** (.r1 ↦ᵣ x)) := by
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ b) (pcFree_regIs _ _)
    (jsgt_imm_spec .r1 12 x 119 126).toBranch
  exact cuTripleWithin_weaken (fun _ h => h) (ite_post .r0)
    (cuTripleWithinBranch_join (by sl_disjoint_codereq) (by sl_disjoint_codereq)
      (by sl_disjoint_codereq) h_br (n126 b x) (n120 b x))

/-- The value fn 116 leaves in `r0`, as a function of the error payload `b` (r2) and the
    32-bit error variant `x` (r1 after `lsh 32; rsh 32`). -/
def convVal (b x : Nat) : Nat := (if toSigned64 x > toSigned64 (toU64 12) then (if toSigned64 x ≤ toSigned64 (toU64 18) then (if toSigned64 x > toSigned64 (toU64 15) then (if x = toU64 16 then toU64 73014444032 else (if x ≠ toU64 17 then toU64 81604378624 else toU64 77309411328)) else (if x = toU64 13 then toU64 60129542144 else (if x ≠ toU64 14 then toU64 68719476736 else toU64 64424509440))) else (if toSigned64 x ≤ toSigned64 (toU64 21) then (if x = toU64 19 then toU64 85899345920 else (if x ≠ toU64 20 then toU64 94489280512 else toU64 90194313216)) else (if toSigned64 x > toSigned64 (toU64 23) then (if x ≠ toU64 24 then toU64 111669149696 else toU64 107374182400) else (if x ≠ toU64 22 then toU64 103079215104 else toU64 98784247808)))) else (if toSigned64 x ≤ toSigned64 (toU64 5) then (if toSigned64 x > toSigned64 (toU64 2) then (if x = toU64 3 then toU64 17179869184 else (if x ≠ toU64 4 then toU64 25769803776 else toU64 21474836480)) else (if x = toU64 0 then (if (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≠ toU64 0 then (((b <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) else toU64 4294967296) else (if x = toU64 1 then toU64 8589934592 else toU64 12884901888))) else (if toSigned64 x ≤ toSigned64 (toU64 8) then (if x = toU64 6 then toU64 30064771072 else (if x ≠ toU64 7 then toU64 38654705664 else toU64 34359738368)) else (if toSigned64 x > toSigned64 (toU64 10) then (if x ≠ toU64 11 then toU64 55834574848 else toU64 51539607552) else (if x ≠ toU64 9 then toU64 47244640256 else toU64 42949672960)))))

/-- The decision tree's code requirement (PCs 119-196). -/
def crTree : CodeReq := ((((CodeReq.singleton 119 (.jsgt .r1 (.imm 12) 126))).union ((((CodeReq.singleton 126 (.jsle .r1 (.imm 18) 138))).union ((((CodeReq.singleton 138 (.jsgt .r1 (.imm 15) 155))).union ((((CodeReq.singleton 155 (.jeq .r1 (.imm 16) 178))).union (((CodeReq.singleton 178 (.lddw .r0 73014444032)).union (CodeReq.singleton 179 (.ja 197))))).union ((((CodeReq.singleton 156 (.jne .r1 (.imm 17) 196))).union ((CodeReq.singleton 196 (.lddw .r0 81604378624)))).union (((CodeReq.singleton 157 (.lddw .r0 77309411328)).union (CodeReq.singleton 158 (.ja 197))))))).union ((((CodeReq.singleton 139 (.jeq .r1 (.imm 13) 174))).union (((CodeReq.singleton 174 (.lddw .r0 60129542144)).union (CodeReq.singleton 175 (.ja 197))))).union ((((CodeReq.singleton 140 (.jne .r1 (.imm 14) 192))).union (((CodeReq.singleton 192 (.lddw .r0 68719476736)).union (CodeReq.singleton 193 (.ja 197))))).union (((CodeReq.singleton 141 (.lddw .r0 64424509440)).union (CodeReq.singleton 142 (.ja 197)))))))).union ((((CodeReq.singleton 127 (.jsle .r1 (.imm 21) 147))).union ((((CodeReq.singleton 147 (.jeq .r1 (.imm 19) 167))).union (((CodeReq.singleton 167 (.lddw .r0 85899345920)).union (CodeReq.singleton 168 (.ja 197))))).union ((((CodeReq.singleton 148 (.jne .r1 (.imm 20) 182))).union (((CodeReq.singleton 182 (.lddw .r0 94489280512)).union (CodeReq.singleton 183 (.ja 197))))).union (((CodeReq.singleton 149 (.lddw .r0 90194313216)).union (CodeReq.singleton 150 (.ja 197))))))).union ((((CodeReq.singleton 128 (.jsgt .r1 (.imm 23) 162))).union ((((CodeReq.singleton 162 (.jne .r1 (.imm 24) 190))).union (((CodeReq.singleton 190 (.lddw .r0 111669149696)).union (CodeReq.singleton 191 (.ja 197))))).union (((CodeReq.singleton 163 (.lddw .r0 107374182400)).union (CodeReq.singleton 164 (.ja 197)))))).union ((((CodeReq.singleton 129 (.jne .r1 (.imm 22) 186))).union (((CodeReq.singleton 186 (.lddw .r0 103079215104)).union (CodeReq.singleton 187 (.ja 197))))).union (((CodeReq.singleton 130 (.lddw .r0 98784247808)).union (CodeReq.singleton 131 (.ja 197))))))))).union ((((CodeReq.singleton 120 (.jsle .r1 (.imm 5) 132))).union ((((CodeReq.singleton 132 (.jsgt .r1 (.imm 2) 151))).union ((((CodeReq.singleton 151 (.jeq .r1 (.imm 3) 176))).union (((CodeReq.singleton 176 (.lddw .r0 17179869184)).union (CodeReq.singleton 177 (.ja 197))))).union ((((CodeReq.singleton 152 (.jne .r1 (.imm 4) 194))).union (((CodeReq.singleton 194 (.lddw .r0 25769803776)).union (CodeReq.singleton 195 (.ja 197))))).union (((CodeReq.singleton 153 (.lddw .r0 21474836480)).union (CodeReq.singleton 154 (.ja 197))))))).union ((((CodeReq.singleton 133 (.jeq .r1 (.imm 0) 169))).union ((((CodeReq.singleton 169 (.lsh64 .r0 (.imm 32)))).union (CodeReq.singleton 170 (.rsh64 .r0 (.imm 32)))).union ((((CodeReq.singleton 171 (.jne .r0 (.imm 0) 197))).union CodeReq.empty).union (((CodeReq.singleton 172 (.lddw .r0 4294967296)).union (CodeReq.singleton 173 (.ja 197))))))).union (((CodeReq.singleton 134 (.lddw .r0 8589934592))).union ((((CodeReq.singleton 135 (.jeq .r1 (.imm 1) 197))).union CodeReq.empty).union (((CodeReq.singleton 136 (.lddw .r0 12884901888)).union (CodeReq.singleton 137 (.ja 197))))))))).union ((((CodeReq.singleton 121 (.jsle .r1 (.imm 8) 143))).union ((((CodeReq.singleton 143 (.jeq .r1 (.imm 6) 165))).union (((CodeReq.singleton 165 (.lddw .r0 30064771072)).union (CodeReq.singleton 166 (.ja 197))))).union ((((CodeReq.singleton 144 (.jne .r1 (.imm 7) 180))).union (((CodeReq.singleton 180 (.lddw .r0 38654705664)).union (CodeReq.singleton 181 (.ja 197))))).union (((CodeReq.singleton 145 (.lddw .r0 34359738368)).union (CodeReq.singleton 146 (.ja 197))))))).union ((((CodeReq.singleton 122 (.jsgt .r1 (.imm 10) 159))).union ((((CodeReq.singleton 159 (.jne .r1 (.imm 11) 188))).union (((CodeReq.singleton 188 (.lddw .r0 55834574848)).union (CodeReq.singleton 189 (.ja 197))))).union (((CodeReq.singleton 160 (.lddw .r0 51539607552)).union (CodeReq.singleton 161 (.ja 197)))))).union ((((CodeReq.singleton 123 (.jne .r1 (.imm 9) 184))).union (((CodeReq.singleton 184 (.lddw .r0 47244640256)).union (CodeReq.singleton 185 (.ja 197))))).union (((CodeReq.singleton 124 (.lddw .r0 42949672960)).union (CodeReq.singleton 125 (.ja 197)))))))))

/-- `r1` after the prologue's `lsh64 r1 32; rsh64 r1 32`: the low 32 bits of the variant. -/
def variant32 (a : Nat) : Nat := ((a <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)

theorem tree_spec (b x : Nat) :
    cuTripleWithin 9 0 119 197 crTree
      ((.r0 ↦ᵣ b) ** (.r1 ↦ᵣ x)) ((.r0 ↦ᵣ convVal b x) ** (.r1 ↦ᵣ x)) :=
  n119 b x

/-- fn 116 from its entry to its `exit` (PC 197): `r0 = convVal r2 (variant32 r1)`. -/
theorem error_convert_spec (v0 a b : Nat) :
    cuTripleWithin 12 0 116 197
      ((((CodeReq.singleton 116 (.mov64 .r0 (.reg .r2))).union
          (CodeReq.singleton 117 (.lsh64 .r1 (.imm 32)))).union
          (CodeReq.singleton 118 (.rsh64 .r1 (.imm 32)))).union crTree)
      ((.r0 ↦ᵣ v0) ** (.r1 ↦ᵣ a) ** (.r2 ↦ᵣ b))
      ((.r0 ↦ᵣ convVal b (variant32 a)) ** (.r1 ↦ᵣ variant32 a) ** (.r2 ↦ᵣ b)) := by
  have h0 := mov64_reg_spec .r0 .r2 v0 b 116 (by decide)
  have h1 := lsh64_imm_spec .r1 32 a 117 (by decide)
  have h2 := rsh64_imm_spec .r1 32 ((a <<< (toU64 32 % 64)) % U64_MODULUS) 118 (by decide)
  have h3 := tree_spec b (variant32 a)
  unfold crTree at h3 ⊢
  unfold variant32 at h3 ⊢
  sl_block_iter [h0, h1, h2, h3]

/-- The conversion never produces 0: every `Err` exits the program with a nonzero code. -/
theorem convVal_ne_zero (b x : Nat) : convVal b x ≠ 0 := by
  unfold convVal
  repeat' split
  all_goals first
    | decide
    | (intro hz; apply (‹_ ≠ toU64 0›); rw [hz]; decide)

end Examples.PTokenErrorConvert
