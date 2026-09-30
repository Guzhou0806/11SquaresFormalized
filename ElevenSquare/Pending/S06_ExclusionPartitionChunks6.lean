import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good24 : BaselineGood baselineArrayChunk24 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block24 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block24 returned_block0 (by decide))
      (blocks_disjoint baseline_block24 returned_block1 (by decide)))
      (blocks_disjoint baseline_block24 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block24 candidate_block (by decide)
#print axioms baseline_good24
theorem baseline_good25 : BaselineGood baselineArrayChunk25 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block25 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block25 returned_block0 (by decide))
      (blocks_disjoint baseline_block25 returned_block1 (by decide)))
      (blocks_disjoint baseline_block25 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block25 candidate_block (by decide)
#print axioms baseline_good25
theorem baseline_good26 : BaselineGood baselineArrayChunk26 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block26 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block26 returned_block0 (by decide))
      (blocks_disjoint baseline_block26 returned_block1 (by decide)))
      (blocks_disjoint baseline_block26 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block26 candidate_block (by decide)
#print axioms baseline_good26
theorem baseline_good27 : BaselineGood baselineArrayChunk27 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block27 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block27 returned_block0 (by decide))
      (blocks_disjoint baseline_block27 returned_block1 (by decide)))
      (blocks_disjoint baseline_block27 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block27 candidate_block (by decide)
#print axioms baseline_good27
end ElevenSquare.Pending.ExclusionCounts
