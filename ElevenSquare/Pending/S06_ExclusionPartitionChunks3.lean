import ElevenSquare.Pending.S06_ExclusionPartitionSupport
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_good12 : BaselineGood baselineArrayChunk12 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block12 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block12 returned_block0 (by decide))
      (blocks_disjoint baseline_block12 returned_block1 (by decide)))
      (blocks_disjoint baseline_block12 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block12 candidate_block (by decide)
#print axioms baseline_good12
theorem baseline_good13 : BaselineGood baselineArrayChunk13 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block13 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block13 returned_block0 (by decide))
      (blocks_disjoint baseline_block13 returned_block1 (by decide)))
      (blocks_disjoint baseline_block13 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block13 candidate_block (by decide)
#print axioms baseline_good13
theorem baseline_good14 : BaselineGood baselineArrayChunk14 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block14 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block14 returned_block0 (by decide))
      (blocks_disjoint baseline_block14 returned_block1 (by decide)))
      (blocks_disjoint baseline_block14 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block14 candidate_block (by decide)
#print axioms baseline_good14
theorem baseline_good15 : BaselineGood baselineArrayChunk15 := by
  refine ⟨bounded_sound _ _ (by decide), ?_, ?_, ?_⟩
  · exact blocks_disjoint baseline_block15 prior_prefix1 (by decide)
  · exact disjoint_array_append (disjoint_array_append
      (blocks_disjoint baseline_block15 returned_block0 (by decide))
      (blocks_disjoint baseline_block15 returned_block1 (by decide)))
      (blocks_disjoint baseline_block15 returned_block2 (by decide))
  · exact blocks_disjoint baseline_block15 candidate_block (by decide)
#print axioms baseline_good15
end ElevenSquare.Pending.ExclusionCounts
