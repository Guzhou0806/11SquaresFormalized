import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061.MedianCapture0
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061.MedianChecks1

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def pairs1 : Finset (QPoint × QPoint) := {(site02,site06), (site02,site07), (site06,site07)}
theorem pair_cover1 : ∀ a ∈ featureB, ∀ b ∈ featureB, a ≠ b →
    (a,b) ∈ pairs1 ∨ (b,a) ∈ pairs1 := by
  intro a ha b hb hab
  simp only [featureB, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    simp [pairs1] at *

theorem axis_checks1 : ∀ n ∈ ([referenceAxisQ referenceAngle,
      rationalNeg (referenceAxisQ referenceAngle),
      rationalPerp (referenceAxisQ referenceAngle),
      rationalNeg (rationalPerp (referenceAxisQ referenceAngle))] : List QPoint),
    FixedMedianFacetCheck featureB 2 (referenceAxisQ referenceAngle)
      coreHalf medianTarget1 n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact facet1_check_000
  · exact facet1_check_001
  · exact facet1_check_002
  · exact facet1_check_003

theorem pair_checks1 : ∀ ab ∈ pairs1,
    FixedMedianFacetCheck featureB 2 (referenceAxisQ referenceAngle)
      coreHalf medianTarget1 (pairWorldQ ab.1 ab.2) ∧
    FixedMedianFacetCheck featureB 2 (referenceAxisQ referenceAngle)
      coreHalf medianTarget1 (rationalNeg (pairWorldQ ab.1 ab.2)) := by
  intro ab hab
  simp only [pairs1, Finset.mem_insert, Finset.mem_singleton] at hab
  rcases hab with rfl | rfl | rfl
  · exact ⟨facet1_check_004, facet1_check_005⟩
  · exact ⟨facet1_check_006, facet1_check_007⟩
  · exact ⟨facet1_check_008, facet1_check_009⟩

theorem median_target1_majority (q : UnitSquare)
    (hq : inputRow.contains q)
    (hcenter : q.center ∈ medianTarget1.carrier) :
    BaselineMajorityCapture featureB 2 q := by
  obtain ⟨_,t,_,_,hlo,hhi,ha⟩ := hq
  exact fixed_core_majority_of_target featureB pairs1 2 q
    referenceAngle coreHalf inputRow.lo inputRow.hi t medianTarget1
    (by norm_num [coreHalf]) (by norm_num) hlo hhi ha hcenter
    pair_cover1 axis_checks1 pair_checks1
    corner_pp corner_pn corner_np corner_nn

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061.median_target1_majority
