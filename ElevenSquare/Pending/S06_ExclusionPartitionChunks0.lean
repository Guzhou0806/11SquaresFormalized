import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good0 : BaselineGood baselineArrayChunk0 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block0 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block0 returned_block0 (by decide))
      (blocks_disjoint baseline_block0 returned_block1 (by decide)))
      (blocks_disjoint baseline_block0 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block0 candidate_block (by decide)
#print axioms baseline_good0
theorem baseline_good1 : BaselineGood baselineArrayChunk1 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block1 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block1 returned_block0 (by decide))
      (blocks_disjoint baseline_block1 returned_block1 (by decide)))
      (blocks_disjoint baseline_block1 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block1 candidate_block (by decide)
#print axioms baseline_good1
theorem baseline_good2 : BaselineGood baselineArrayChunk2 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block2 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block2 returned_block0 (by decide))
      (blocks_disjoint baseline_block2 returned_block1 (by decide)))
      (blocks_disjoint baseline_block2 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block2 candidate_block (by decide)
#print axioms baseline_good2
theorem baseline_good3 : BaselineGood baselineArrayChunk3 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block3 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block3 returned_block0 (by decide))
      (blocks_disjoint baseline_block3 returned_block1 (by decide)))
      (blocks_disjoint baseline_block3 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block3 candidate_block (by decide)
#print axioms baseline_good3
end ElevenSquare.Pending.ExclusionCounts
