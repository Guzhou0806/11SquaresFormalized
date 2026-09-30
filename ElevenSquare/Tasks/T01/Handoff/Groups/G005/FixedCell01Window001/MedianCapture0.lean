import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001.Core
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001.MedianChecks0

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def pairs : Finset (QPoint × QPoint) :=
  {(site00,site01), (site00,site03), (site00,site04), (site00,site05), (site01,site03), (site01,site04), (site01,site05), (site03,site04), (site03,site05), (site04,site05)}

theorem pair_cover : ∀ a ∈ featureA, ∀ b ∈ featureA, a ≠ b →
    (a,b) ∈ pairs ∨ (b,a) ∈ pairs := by
  intro a ha b hb hab
  simp only [featureA, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp [pairs] at *

theorem axis_checks : ∀ n ∈ ([referenceAxisQ referenceAngle,
      rationalNeg (referenceAxisQ referenceAngle),
      rationalPerp (referenceAxisQ referenceAngle),
      rationalNeg (rationalPerp (referenceAxisQ referenceAngle))] : List QPoint),
    FixedMedianFacetCheck featureA 3 (referenceAxisQ referenceAngle)
      coreHalf medianTarget0 n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact facet0_check_000
  · exact facet0_check_001
  · exact facet0_check_002
  · exact facet0_check_003

theorem pair_checks : ∀ ab ∈ pairs,
    FixedMedianFacetCheck featureA 3 (referenceAxisQ referenceAngle)
      coreHalf medianTarget0 (pairWorldQ ab.1 ab.2) ∧
    FixedMedianFacetCheck featureA 3 (referenceAxisQ referenceAngle)
      coreHalf medianTarget0 (rationalNeg (pairWorldQ ab.1 ab.2)) := by
  intro ab hab
  simp only [pairs, Finset.mem_insert, Finset.mem_singleton] at hab
  rcases hab with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨facet0_check_004, facet0_check_005⟩
  · exact ⟨facet0_check_006, facet0_check_007⟩
  · exact ⟨facet0_check_008, facet0_check_009⟩
  · exact ⟨facet0_check_010, facet0_check_011⟩
  · exact ⟨facet0_check_012, facet0_check_013⟩
  · exact ⟨facet0_check_014, facet0_check_015⟩
  · exact ⟨facet0_check_016, facet0_check_017⟩
  · exact ⟨facet0_check_018, facet0_check_019⟩
  · exact ⟨facet0_check_020, facet0_check_021⟩
  · exact ⟨facet0_check_022, facet0_check_023⟩

theorem corner_pp : BaselineCoreVertexCheck
    (referenceCorner referenceAngle coreHalf 1 1) inputRow.lo inputRow.hi := by
  apply core_checked
  norm_num [core, referenceAngle, coreHalf, referenceCorner]

theorem corner_pn : BaselineCoreVertexCheck
    (referenceCorner referenceAngle coreHalf 1 (-1)) inputRow.lo inputRow.hi := by
  apply core_checked
  norm_num [core, referenceAngle, coreHalf, referenceCorner]

theorem corner_np : BaselineCoreVertexCheck
    (referenceCorner referenceAngle coreHalf (-1) 1) inputRow.lo inputRow.hi := by
  apply core_checked
  norm_num [core, referenceAngle, coreHalf, referenceCorner]

theorem corner_nn : BaselineCoreVertexCheck
    (referenceCorner referenceAngle coreHalf (-1) (-1)) inputRow.lo inputRow.hi := by
  apply core_checked
  norm_num [core, referenceAngle, coreHalf, referenceCorner]

theorem median_target0_majority (q : UnitSquare)
    (hq : inputRow.contains q)
    (hcenter : q.center ∈ medianTarget0.carrier) :
    BaselineMajorityCapture featureA 3 q := by
  obtain ⟨_,t,_,_,hlo,hhi,ha⟩ := hq
  exact fixed_core_majority_of_target featureA pairs 3 q
    referenceAngle coreHalf inputRow.lo inputRow.hi t medianTarget0
    (by norm_num [coreHalf]) (by norm_num) hlo hhi ha hcenter
    pair_cover axis_checks pair_checks corner_pp corner_pn corner_np corner_nn

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001.median_target0_majority
