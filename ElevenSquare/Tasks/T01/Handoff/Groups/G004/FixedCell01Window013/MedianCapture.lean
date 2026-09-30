import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window013.Core
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window013.MedianChecks

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window013
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def pairs : Finset (QPoint × QPoint) :=
  {(site00,site01), (site00,site02), (site00,site03), (site00,site04),
   (site01,site02), (site01,site03), (site01,site04),
   (site02,site03), (site02,site04), (site03,site04)}

theorem pair_cover : ∀ a ∈ featureSites, ∀ b ∈ featureSites, a ≠ b →
    (a,b) ∈ pairs ∨ (b,a) ∈ pairs := by
  intro a ha b hb hab
  simp only [featureSites, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp [pairs] at *

theorem axis_checks : ∀ n ∈ ([referenceAxisQ referenceAngle,
      rationalNeg (referenceAxisQ referenceAngle),
      rationalPerp (referenceAxisQ referenceAngle),
      rationalNeg (rationalPerp (referenceAxisQ referenceAngle))] : List QPoint),
    FixedMedianFacetCheck featureSites 3 (referenceAxisQ referenceAngle)
      coreHalf medianTarget n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact facet_check_000
  · exact facet_check_001
  · exact facet_check_002
  · exact facet_check_003

theorem pair_checks : ∀ ab ∈ pairs,
    FixedMedianFacetCheck featureSites 3 (referenceAxisQ referenceAngle)
      coreHalf medianTarget (pairWorldQ ab.1 ab.2) ∧
    FixedMedianFacetCheck featureSites 3 (referenceAxisQ referenceAngle)
      coreHalf medianTarget (rationalNeg (pairWorldQ ab.1 ab.2)) := by
  intro ab hab
  simp only [pairs, Finset.mem_insert, Finset.mem_singleton] at hab
  rcases hab with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨facet_check_004, facet_check_005⟩
  · exact ⟨facet_check_006, facet_check_007⟩
  · exact ⟨facet_check_008, facet_check_009⟩
  · exact ⟨facet_check_010, facet_check_011⟩
  · exact ⟨facet_check_012, facet_check_013⟩
  · exact ⟨facet_check_014, facet_check_015⟩
  · exact ⟨facet_check_016, facet_check_017⟩
  · exact ⟨facet_check_018, facet_check_019⟩
  · exact ⟨facet_check_020, facet_check_021⟩
  · exact ⟨facet_check_022, facet_check_023⟩

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

theorem median_target_majority (q : UnitSquare)
    (hq : inputRow.contains q)
    (hcenter : q.center ∈ medianTarget.carrier) :
    BaselineMajorityCapture featureSites 3 q := by
  obtain ⟨_,t,_,_,hlo,hhi,ha⟩ := hq
  exact fixed_core_majority_of_target featureSites pairs 3 q
    referenceAngle coreHalf inputRow.lo inputRow.hi t medianTarget
    (by norm_num [coreHalf]) (by norm_num) hlo hhi ha hcenter
    pair_cover axis_checks pair_checks corner_pp corner_pn corner_np corner_nn

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window013

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window013.median_target_majority
