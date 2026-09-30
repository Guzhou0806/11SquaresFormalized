import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good8 : BaselineGood baselineArrayChunk8 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block8 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block8 returned_block0 (by decide))
      (blocks_disjoint baseline_block8 returned_block1 (by decide)))
      (blocks_disjoint baseline_block8 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block8 candidate_block (by decide)
#print axioms baseline_good8
theorem baseline_good9 : BaselineGood baselineArrayChunk9 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block9 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block9 returned_block0 (by decide))
      (blocks_disjoint baseline_block9 returned_block1 (by decide)))
      (blocks_disjoint baseline_block9 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block9 candidate_block (by decide)
#print axioms baseline_good9
theorem baseline_good10 : BaselineGood baselineArrayChunk10 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block10 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block10 returned_block0 (by decide))
      (blocks_disjoint baseline_block10 returned_block1 (by decide)))
      (blocks_disjoint baseline_block10 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block10 candidate_block (by decide)
#print axioms baseline_good10
theorem baseline_good11 : BaselineGood baselineArrayChunk11 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block11 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block11 returned_block0 (by decide))
      (blocks_disjoint baseline_block11 returned_block1 (by decide)))
      (blocks_disjoint baseline_block11 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block11 candidate_block (by decide)
#print axioms baseline_good11
end ElevenSquare.Pending.ExclusionCounts
