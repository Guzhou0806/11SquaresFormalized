import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck00
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck01
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck02
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck03
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck04
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck05
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck06
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck07
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck08
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianCheck09

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def medianPairs : Finset (QPoint × QPoint) :=
  {(G005.site02, G005.site06), (G005.site02, G005.site07),
    (G005.site06, G005.site07)}
def medianCerts : List MedianFacetCertificate :=
  [medCert00, medCert01, medCert02, medCert03, medCert04, medCert05, medCert06, medCert07, medCert08, medCert09]
def medianTargetCert : MedianTargetCertificate := ⟨medianPairs, medianCerts⟩

theorem medianTargetCert_checked :
    medianTargetCert.Check G005.featureB 2 target half left right := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [medianTargetCert, medianCerts, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact medCert00_checked
    · exact medCert01_checked
    · exact medCert02_checked
    · exact medCert03_checked
    · exact medCert04_checked
    · exact medCert05_checked
    · exact medCert06_checked
    · exact medCert07_checked
    · exact medCert08_checked
    · exact medCert09_checked
  · intro d hd
    simp only [medianAxisDirections, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨medCert00, by simp [medianTargetCert, medianCerts], rfl⟩
    · exact ⟨medCert01, by simp [medianTargetCert, medianCerts], rfl⟩
    · exact ⟨medCert02, by simp [medianTargetCert, medianCerts], rfl⟩
    · exact ⟨medCert03, by simp [medianTargetCert, medianCerts], rfl⟩
  · intro ab hab negative
    simp only [medianTargetCert, medianPairs, Finset.mem_insert,
      Finset.mem_singleton] at hab
    rcases hab with rfl | rfl | rfl
    · cases negative
      · exact ⟨medCert04, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert05, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert06, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert07, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert08, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert09, by simp [medianTargetCert, medianCerts], rfl⟩
  · intro a ha b hb hab
    simp only [G005.featureB, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl
    all_goals rcases hb with rfl | rfl | rfl
    all_goals simp [medianTargetCert, medianPairs] at *

theorem majority_of_target (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ))
    (hcontains : SymbolicPolygonContains target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  exact median_target_certificate_sound medianTargetCert G005.featureB 2
    target half left right medianTargetCert_checked q t ha hlt htu
    (by norm_num [half]) (by norm_num) hcontains

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
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.captures_square
