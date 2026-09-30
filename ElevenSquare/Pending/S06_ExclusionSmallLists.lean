import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData

theorem prior_bound : ∀ x ∈ priorArray.toList, x < 2184 := bounded_sound _ _ (by decide)
theorem returned_bound : ∀ x ∈ returnedArray.toList, x < 2184 := by
  have h0 : ∀ x ∈ returnedArrayChunk0.toList, x < 2184 := bounded_sound _ _ (by decide)
  have h1 : ∀ x ∈ returnedArrayChunk1.toList, x < 2184 := bounded_sound _ _ (by decide)
  have h2 : ∀ x ∈ returnedArrayChunk2.toList, x < 2184 := bounded_sound _ _ (by decide)
  intro x hx
  simp only [returnedArray, array_toList_append, List.mem_append] at hx
  exact hx.elim (fun h => h.elim (h0 x) (h1 x)) (h2 x)
theorem candidate_bound : ∀ x ∈ candidateArray.toList, x < 2184 := bounded_sound _ _ (by decide)
theorem prior_returned_disjoint : priorArray.toList.Disjoint returnedArray.toList :=
  disjoint_array_append (disjoint_array_append
    (blocks_disjoint prior_prefix1 returned_block0 (by decide))
    (blocks_disjoint prior_prefix1 returned_block1 (by decide)))
    (blocks_disjoint prior_prefix1 returned_block2 (by decide))
theorem prior_candidate_disjoint : priorArray.toList.Disjoint candidateArray.toList :=
  blocks_disjoint prior_prefix1 candidate_block (by decide)
theorem returned_candidate_disjoint : returnedArray.toList.Disjoint candidateArray.toList :=
  (disjoint_array_append (disjoint_array_append
    (blocks_disjoint candidate_block returned_block0 (by decide))
    (blocks_disjoint candidate_block returned_block1 (by decide)))
    (blocks_disjoint candidate_block returned_block2 (by decide))).symm
theorem candidate_card : candidateIndices.card = 4 := candidate_block.card

end ElevenSquare.Pending.ExclusionCounts
#print axioms ElevenSquare.Pending.ExclusionCounts.prior_returned_disjoint
#print axioms ElevenSquare.Pending.ExclusionCounts.returned_candidate_disjoint
#print axioms ElevenSquare.Pending.ExclusionCounts.prior_bound
#print axioms ElevenSquare.Pending.ExclusionCounts.returned_bound
#print axioms ElevenSquare.Pending.ExclusionCounts.candidate_bound
#print axioms ElevenSquare.Pending.ExclusionCounts.candidate_card
