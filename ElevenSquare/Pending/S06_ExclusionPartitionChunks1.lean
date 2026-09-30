import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good4 : BaselineGood baselineArrayChunk4 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block4 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block4 returned_block0 (by decide))
      (blocks_disjoint baseline_block4 returned_block1 (by decide)))
      (blocks_disjoint baseline_block4 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block4 candidate_block (by decide)
#print axioms baseline_good4
theorem baseline_good5 : BaselineGood baselineArrayChunk5 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block5 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block5 returned_block0 (by decide))
      (blocks_disjoint baseline_block5 returned_block1 (by decide)))
      (blocks_disjoint baseline_block5 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block5 candidate_block (by decide)
#print axioms baseline_good5
theorem baseline_good6 : BaselineGood baselineArrayChunk6 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block6 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block6 returned_block0 (by decide))
      (blocks_disjoint baseline_block6 returned_block1 (by decide)))
      (blocks_disjoint baseline_block6 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block6 candidate_block (by decide)
#print axioms baseline_good6
theorem baseline_good7 : BaselineGood baselineArrayChunk7 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block7 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block7 returned_block0 (by decide))
      (blocks_disjoint baseline_block7 returned_block1 (by decide)))
      (blocks_disjoint baseline_block7 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block7 candidate_block (by decide)
#print axioms baseline_good7
end ElevenSquare.Pending.ExclusionCounts
