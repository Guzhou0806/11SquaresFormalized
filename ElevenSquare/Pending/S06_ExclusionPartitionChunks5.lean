import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good20 : BaselineGood baselineArrayChunk20 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block20 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block20 returned_block0 (by decide))
      (blocks_disjoint baseline_block20 returned_block1 (by decide)))
      (blocks_disjoint baseline_block20 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block20 candidate_block (by decide)
#print axioms baseline_good20
theorem baseline_good21 : BaselineGood baselineArrayChunk21 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block21 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block21 returned_block0 (by decide))
      (blocks_disjoint baseline_block21 returned_block1 (by decide)))
      (blocks_disjoint baseline_block21 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block21 candidate_block (by decide)
#print axioms baseline_good21
theorem baseline_good22 : BaselineGood baselineArrayChunk22 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block22 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block22 returned_block0 (by decide))
      (blocks_disjoint baseline_block22 returned_block1 (by decide)))
      (blocks_disjoint baseline_block22 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block22 candidate_block (by decide)
#print axioms baseline_good22
theorem baseline_good23 : BaselineGood baselineArrayChunk23 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block23 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block23 returned_block0 (by decide))
      (blocks_disjoint baseline_block23 returned_block1 (by decide)))
      (blocks_disjoint baseline_block23 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block23 candidate_block (by decide)
#print axioms baseline_good23
end ElevenSquare.Pending.ExclusionCounts
