import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good16 : BaselineGood baselineArrayChunk16 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block16 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block16 returned_block0 (by decide))
      (blocks_disjoint baseline_block16 returned_block1 (by decide)))
      (blocks_disjoint baseline_block16 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block16 candidate_block (by decide)
#print axioms baseline_good16
theorem baseline_good17 : BaselineGood baselineArrayChunk17 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block17 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block17 returned_block0 (by decide))
      (blocks_disjoint baseline_block17 returned_block1 (by decide)))
      (blocks_disjoint baseline_block17 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block17 candidate_block (by decide)
#print axioms baseline_good17
theorem baseline_good18 : BaselineGood baselineArrayChunk18 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block18 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block18 returned_block0 (by decide))
      (blocks_disjoint baseline_block18 returned_block1 (by decide)))
      (blocks_disjoint baseline_block18 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block18 candidate_block (by decide)
#print axioms baseline_good18
theorem baseline_good19 : BaselineGood baselineArrayChunk19 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block19 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block19 returned_block0 (by decide))
      (blocks_disjoint baseline_block19 returned_block1 (by decide)))
      (blocks_disjoint baseline_block19 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block19 candidate_block (by decide)
#print axioms baseline_good19
end ElevenSquare.Pending.ExclusionCounts
