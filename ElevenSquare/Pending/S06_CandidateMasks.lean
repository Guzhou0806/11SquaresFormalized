import ElevenSquare.Pending.S06_CandidateLookup438
import ElevenSquare.Pending.S06_CandidateLookup999
import ElevenSquare.Pending.S06_CandidateLookup1462
import ElevenSquare.Pending.S06_CandidateLookup1659

namespace ElevenSquare.Pending
def candidateTupleMask (row : List ℕ) : Finset (Fin 16) :=
  (row.map (fun j => (⟨j % 16, Nat.mod_lt j (by decide)⟩ : Fin 16))).toFinset
theorem tuple_index_cast {α : Type} [Inhabited α] (xs : Array α) (k : ℕ)
    (hk : k < 2184) (row : α) (h : xs[k]! = row) :
    xs[(⟨k, hk⟩ : Fin 2184).val]! = row := h
theorem caseMask_eq_of_tuple (k : Fin 2184) (row : List ℕ)
    (h : recordedCaseTuples[k.val]! = row) : caseMask k = candidateTupleMask row := by
  unfold caseMask candidateTupleMask
  rw [h]

theorem candidate_mask_438 : caseMask ⟨438, by omega⟩ = {0, 1, 2, 3, 4, 8, 9, 10, 11, 13, 15} := by
  calc caseMask ⟨438, by omega⟩ = candidateTupleMask [0, 1, 2, 3, 4, 8, 9, 10, 11, 13, 15] :=
      caseMask_eq_of_tuple ⟨438, by omega⟩ _ (tuple_index_cast recordedCaseTuples 438 (by omega) _ CandidateLookup.tuple_438)
    _ = {0, 1, 2, 3, 4, 8, 9, 10, 11, 13, 15} := by simp only [candidateTupleMask, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil] <;> rfl
#print axioms candidate_mask_438

theorem candidate_mask_999 : caseMask ⟨999, by omega⟩ = {0, 1, 2, 4, 6, 7, 9, 10, 12, 14, 15} := by
  calc caseMask ⟨999, by omega⟩ = candidateTupleMask [0, 1, 2, 4, 6, 7, 9, 10, 12, 14, 15] :=
      caseMask_eq_of_tuple ⟨999, by omega⟩ _ (tuple_index_cast recordedCaseTuples 999 (by omega) _ CandidateLookup.tuple_999)
    _ = {0, 1, 2, 4, 6, 7, 9, 10, 12, 14, 15} := by simp only [candidateTupleMask, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil] <;> rfl
#print axioms candidate_mask_999

theorem candidate_mask_1462 : caseMask ⟨1462, by omega⟩ = {0, 1, 3, 5, 6, 8, 9, 11, 12, 13, 14} := by
  calc caseMask ⟨1462, by omega⟩ = candidateTupleMask [0, 1, 3, 5, 6, 8, 9, 11, 12, 13, 14] :=
      caseMask_eq_of_tuple ⟨1462, by omega⟩ _ (tuple_index_cast recordedCaseTuples 1462 (by omega) _ CandidateLookup.tuple_1462)
    _ = {0, 1, 3, 5, 6, 8, 9, 11, 12, 13, 14} := by simp only [candidateTupleMask, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil] <;> rfl
#print axioms candidate_mask_1462

theorem candidate_mask_1659 : caseMask ⟨1659, by omega⟩ = {0, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14} := by
  calc caseMask ⟨1659, by omega⟩ = candidateTupleMask [0, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14] :=
      caseMask_eq_of_tuple ⟨1659, by omega⟩ _ (tuple_index_cast recordedCaseTuples 1659 (by omega) _ CandidateLookup.tuple_1659)
    _ = {0, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14} := by simp only [candidateTupleMask, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil] <;> rfl
#print axioms candidate_mask_1659

theorem recorded_candidate_masks :
    caseMask ⟨438, by omega⟩ = {0,1,2,3,4,8,9,10,11,13,15} ∧
    caseMask ⟨999, by omega⟩ = {0,1,2,4,6,7,9,10,12,14,15} ∧
    caseMask ⟨1462, by omega⟩ = {0,1,3,5,6,8,9,11,12,13,14} ∧
    caseMask ⟨1659, by omega⟩ = {0,2,3,4,5,6,7,11,12,13,14} :=
  ⟨candidate_mask_438, candidate_mask_999, candidate_mask_1462, candidate_mask_1659⟩
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.recorded_candidate_masks
