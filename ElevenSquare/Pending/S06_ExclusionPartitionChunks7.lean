import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good28 : BaselineGood baselineArrayChunk28 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block28 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block28 returned_block0 (by decide))
      (blocks_disjoint baseline_block28 returned_block1 (by decide)))
      (blocks_disjoint baseline_block28 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block28 candidate_block (by decide)
#print axioms baseline_good28
theorem baseline_good29 : BaselineGood baselineArrayChunk29 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block29 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block29 returned_block0 (by decide))
      (blocks_disjoint baseline_block29 returned_block1 (by decide)))
      (blocks_disjoint baseline_block29 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block29 candidate_block (by decide)
#print axioms baseline_good29
theorem baseline_good30 : BaselineGood baselineArrayChunk30 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block30 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block30 returned_block0 (by decide))
      (blocks_disjoint baseline_block30 returned_block1 (by decide)))
      (blocks_disjoint baseline_block30 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block30 candidate_block (by decide)
#print axioms baseline_good30
end ElevenSquare.Pending.ExclusionCounts
