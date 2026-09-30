import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL00
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL01
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL02
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL03
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL04
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL05
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL06
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL07
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL08
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckL09
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR00
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR01
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR02
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR03
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR04
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR05
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR06
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR07
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR08
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianCheckR09

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def medianPairs : Finset (QPoint × QPoint) :=
  {(G005.site02, G005.site06), (G005.site02, G005.site07),
    (G005.site06, G005.site07)}

def medianRefsL : List MedianFacetProofRef :=
  [.guarded guardedL00, .plain medCertL01, .plain medCertL02, .plain medCertL03, .plain medCertL04, .plain medCertL05, .plain medCertL06, .plain medCertL07, .plain medCertL08, .plain medCertL09]
def medianTargetCertL : MixedMedianTargetCertificate :=
  ⟨medianPairs, medianRefsL⟩

theorem medianTargetCertL_checked :
    medianTargetCertL.Check G005.featureB 2 target half guard left right := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [medianTargetCertL, medianRefsL, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact guardedL00_checked
    · exact medCertL01_checked
    · exact medCertL02_checked
    · exact medCertL03_checked
    · exact medCertL04_checked
    · exact medCertL05_checked
    · exact medCertL06_checked
    · exact medCertL07_checked
    · exact medCertL08_checked
    · exact medCertL09_checked
  · intro d hd
    simp only [medianAxisDirections, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨.guarded guardedL00, by simp [medianTargetCertL, medianRefsL], rfl⟩
    · exact ⟨.plain medCertL01, by simp [medianTargetCertL, medianRefsL], rfl⟩
    · exact ⟨.plain medCertL02, by simp [medianTargetCertL, medianRefsL], rfl⟩
    · exact ⟨.plain medCertL03, by simp [medianTargetCertL, medianRefsL], rfl⟩
  · intro ab hab negative
    simp only [medianTargetCertL, medianPairs, Finset.mem_insert,
      Finset.mem_singleton] at hab
    rcases hab with rfl | rfl | rfl
    · cases negative
      · exact ⟨.plain medCertL04, by simp [medianTargetCertL, medianRefsL], rfl⟩
      · exact ⟨.plain medCertL05, by simp [medianTargetCertL, medianRefsL], rfl⟩
    · cases negative
      · exact ⟨.plain medCertL06, by simp [medianTargetCertL, medianRefsL], rfl⟩
      · exact ⟨.plain medCertL07, by simp [medianTargetCertL, medianRefsL], rfl⟩
    · cases negative
      · exact ⟨.plain medCertL08, by simp [medianTargetCertL, medianRefsL], rfl⟩
      · exact ⟨.plain medCertL09, by simp [medianTargetCertL, medianRefsL], rfl⟩
  · intro a ha b hb hab
    simp only [G005.featureB, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl
    all_goals rcases hb with rfl | rfl | rfl
    all_goals simp [medianTargetCertL, medianPairs] at *

theorem majority_L (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ))
    (hguard : 0 ≤ guard.eval t)
    (hcontains : SymbolicPolygonContains target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  exact mixed_median_target_certificate_sound medianTargetCertL
    G005.featureB 2 target half left right guard
    medianTargetCertL_checked q t ha hlt htu hguard
    (by norm_num [half]) (by norm_num) hcontains

def medianRefsR : List MedianFacetProofRef :=
  [.guarded guardedR00, .plain medCertR01, .plain medCertR02, .plain medCertR03, .plain medCertR04, .plain medCertR05, .plain medCertR06, .plain medCertR07, .plain medCertR08, .plain medCertR09]
def medianTargetCertR : MixedMedianTargetCertificate :=
  ⟨medianPairs, medianRefsR⟩

theorem medianTargetCertR_checked :
    medianTargetCertR.Check G005.featureB 2 target half negativeGuard left right := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [medianTargetCertR, medianRefsR, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact guardedR00_checked
    · exact medCertR01_checked
    · exact medCertR02_checked
    · exact medCertR03_checked
    · exact medCertR04_checked
    · exact medCertR05_checked
    · exact medCertR06_checked
    · exact medCertR07_checked
    · exact medCertR08_checked
    · exact medCertR09_checked
  · intro d hd
    simp only [medianAxisDirections, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨.guarded guardedR00, by simp [medianTargetCertR, medianRefsR], rfl⟩
    · exact ⟨.plain medCertR01, by simp [medianTargetCertR, medianRefsR], rfl⟩
    · exact ⟨.plain medCertR02, by simp [medianTargetCertR, medianRefsR], rfl⟩
    · exact ⟨.plain medCertR03, by simp [medianTargetCertR, medianRefsR], rfl⟩
  · intro ab hab negative
    simp only [medianTargetCertR, medianPairs, Finset.mem_insert,
      Finset.mem_singleton] at hab
    rcases hab with rfl | rfl | rfl
    · cases negative
      · exact ⟨.plain medCertR04, by simp [medianTargetCertR, medianRefsR], rfl⟩
      · exact ⟨.plain medCertR05, by simp [medianTargetCertR, medianRefsR], rfl⟩
    · cases negative
      · exact ⟨.plain medCertR06, by simp [medianTargetCertR, medianRefsR], rfl⟩
      · exact ⟨.plain medCertR07, by simp [medianTargetCertR, medianRefsR], rfl⟩
    · cases negative
      · exact ⟨.plain medCertR08, by simp [medianTargetCertR, medianRefsR], rfl⟩
      · exact ⟨.plain medCertR09, by simp [medianTargetCertR, medianRefsR], rfl⟩
  · intro a ha b hb hab
    simp only [G005.featureB, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl
    all_goals rcases hb with rfl | rfl | rfl
    all_goals simp [medianTargetCertR, medianPairs] at *

theorem majority_R (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ))
    (hguard : 0 ≤ negativeGuard.eval t)
    (hcontains : SymbolicPolygonContains target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  exact mixed_median_target_certificate_sound medianTargetCertR
    G005.featureB 2 target half left right negativeGuard
    medianTargetCertR_checked q t ha hlt htu hguard
    (by norm_num [half]) (by norm_num) hcontains


theorem majority_of_target (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ))
    (hcontains : SymbolicPolygonContains target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  rcases le_total 0 (guard.eval t) with hnonneg | hnonpos
  · exact majority_L q t ha hlt htu hnonneg hcontains
  · apply majority_R q t ha hlt htu
    · change 0 ≤ guard.neg.eval t
      rw [symbolic_quadratic_neg_eval]
      linarith
    · exact hcontains

theorem captures_square (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ)) :
    BaselineMajorityCapture G005.featureB 2 q := by
  apply majority_of_target q t ha hlt htu
  apply source_implies_target t hlt htu q.center
  exact symbolic_wall_scaled_slab_contains q 0 t ha hcont hcell

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.captures_square
