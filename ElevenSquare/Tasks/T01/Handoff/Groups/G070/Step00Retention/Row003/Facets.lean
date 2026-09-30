import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row003.FreshCoreData

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row003
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem facet0_implication :
    BaselineImplicationCheck keptRow.centers witness0.translatedCut
      witness0.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness0, RetainedCoreFacetWitness.translatedCut]

theorem facet0_min : witness0.bound = minCoreBound fresh witness0.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness0]

theorem facet0_checked :
    BaselineImplicationCheck keptRow.centers witness0.translatedCut
      witness0.combination ∧
    ∀ p ∈ fresh, witness0.bound ≤
      witness0.facet.c - witness0.facet.a * p.1 - witness0.facet.b * p.2 := by
  refine ⟨facet0_implication, ?_⟩
  intro p hp
  rw [facet0_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness0.facet p hp

theorem facet1_implication :
    BaselineImplicationCheck keptRow.centers witness1.translatedCut
      witness1.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness1, RetainedCoreFacetWitness.translatedCut]

theorem facet1_min : witness1.bound = minCoreBound fresh witness1.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness1]

theorem facet1_checked :
    BaselineImplicationCheck keptRow.centers witness1.translatedCut
      witness1.combination ∧
    ∀ p ∈ fresh, witness1.bound ≤
      witness1.facet.c - witness1.facet.a * p.1 - witness1.facet.b * p.2 := by
  refine ⟨facet1_implication, ?_⟩
  intro p hp
  rw [facet1_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness1.facet p hp

theorem facet2_implication :
    BaselineImplicationCheck keptRow.centers witness2.translatedCut
      witness2.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness2, RetainedCoreFacetWitness.translatedCut]

theorem facet2_min : witness2.bound = minCoreBound fresh witness2.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness2]

theorem facet2_checked :
    BaselineImplicationCheck keptRow.centers witness2.translatedCut
      witness2.combination ∧
    ∀ p ∈ fresh, witness2.bound ≤
      witness2.facet.c - witness2.facet.a * p.1 - witness2.facet.b * p.2 := by
  refine ⟨facet2_implication, ?_⟩
  intro p hp
  rw [facet2_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness2.facet p hp

theorem facet3_implication :
    BaselineImplicationCheck keptRow.centers witness3.translatedCut
      witness3.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness3, RetainedCoreFacetWitness.translatedCut]

theorem facet3_min : witness3.bound = minCoreBound fresh witness3.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness3]

theorem facet3_checked :
    BaselineImplicationCheck keptRow.centers witness3.translatedCut
      witness3.combination ∧
    ∀ p ∈ fresh, witness3.bound ≤
      witness3.facet.c - witness3.facet.a * p.1 - witness3.facet.b * p.2 := by
  refine ⟨facet3_implication, ?_⟩
  intro p hp
  rw [facet3_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness3.facet p hp

theorem facet4_implication :
    BaselineImplicationCheck keptRow.centers witness4.translatedCut
      witness4.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness4, RetainedCoreFacetWitness.translatedCut]

theorem facet4_min : witness4.bound = minCoreBound fresh witness4.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness4]

theorem facet4_checked :
    BaselineImplicationCheck keptRow.centers witness4.translatedCut
      witness4.combination ∧
    ∀ p ∈ fresh, witness4.bound ≤
      witness4.facet.c - witness4.facet.a * p.1 - witness4.facet.b * p.2 := by
  refine ⟨facet4_implication, ?_⟩
  intro p hp
  rw [facet4_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness4.facet p hp

theorem facet5_implication :
    BaselineImplicationCheck keptRow.centers witness5.translatedCut
      witness5.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness5, RetainedCoreFacetWitness.translatedCut]

theorem facet5_min : witness5.bound = minCoreBound fresh witness5.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness5]

theorem facet5_checked :
    BaselineImplicationCheck keptRow.centers witness5.translatedCut
      witness5.combination ∧
    ∀ p ∈ fresh, witness5.bound ≤
      witness5.facet.c - witness5.facet.a * p.1 - witness5.facet.b * p.2 := by
  refine ⟨facet5_implication, ?_⟩
  intro p hp
  rw [facet5_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness5.facet p hp

theorem facet6_implication :
    BaselineImplicationCheck keptRow.centers witness6.translatedCut
      witness6.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness6, RetainedCoreFacetWitness.translatedCut]

theorem facet6_min : witness6.bound = minCoreBound fresh witness6.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness6]

theorem facet6_checked :
    BaselineImplicationCheck keptRow.centers witness6.translatedCut
      witness6.combination ∧
    ∀ p ∈ fresh, witness6.bound ≤
      witness6.facet.c - witness6.facet.a * p.1 - witness6.facet.b * p.2 := by
  refine ⟨facet6_implication, ?_⟩
  intro p hp
  rw [facet6_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness6.facet p hp

theorem facet7_implication :
    BaselineImplicationCheck keptRow.centers witness7.translatedCut
      witness7.combination := by
  norm_num [BaselineImplicationCheck, BaselineCombinationValid,
    baselineCombinationSum, baselineZeroHalfplane, keptRow, kept,
    witness7, RetainedCoreFacetWitness.translatedCut]

theorem facet7_min : witness7.bound = minCoreBound fresh witness7.facet := by
  norm_num [minCoreBound, coreFreshRhs, fresh,
    ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step00.fresh,
    witness7]

theorem facet7_checked :
    BaselineImplicationCheck keptRow.centers witness7.translatedCut
      witness7.combination ∧
    ∀ p ∈ fresh, witness7.bound ≤
      witness7.facet.c - witness7.facet.a * p.1 - witness7.facet.b * p.2 := by
  refine ⟨facet7_implication, ?_⟩
  intro p hp
  rw [facet7_min]
  simpa only [coreFreshRhs] using minCoreBound_le fresh witness7.facet p hp

theorem facets_match : witnesses.map (·.facet) = corePolygon := by
  rfl

theorem facets_checked : ∀ w ∈ witnesses,
    BaselineImplicationCheck keptRow.centers w.translatedCut w.combination ∧
    ∀ p ∈ fresh, w.bound ≤
      w.facet.c - w.facet.a * p.1 - w.facet.b * p.2 := by
  intro w hw
  change w ∈ [witness0, witness1, witness2, witness3,
    witness4, witness5, witness6, witness7] at hw
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact facet0_checked | exact facet1_checked |
    exact facet2_checked | exact facet3_checked | exact facet4_checked |
    exact facet5_checked | exact facet6_checked | exact facet7_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row003.facets_checked
