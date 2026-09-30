import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck00
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck01
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck02
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck03
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck04
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck05
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck06
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck07
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck08
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck09
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck10
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck11
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck12
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck13
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck14
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck15
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck16
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck17
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck18
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck19
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck20
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck21
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck22
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianCheck23

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def medianPairs : Finset (QPoint × QPoint) := {(G005.site00, G005.site01), (G005.site00, G005.site03), (G005.site00, G005.site04), (G005.site00, G005.site05), (G005.site01, G005.site03), (G005.site01, G005.site04), (G005.site01, G005.site05), (G005.site03, G005.site04), (G005.site03, G005.site05), (G005.site04, G005.site05)}
def medianCerts : List MedianFacetCertificate :=
  [medCert00, medCert01, medCert02, medCert03, medCert04, medCert05, medCert06, medCert07, medCert08, medCert09, medCert10, medCert11, medCert12, medCert13, medCert14, medCert15, medCert16, medCert17, medCert18, medCert19, medCert20, medCert21, medCert22, medCert23]
def medianTargetCert : MedianTargetCertificate := ⟨medianPairs, medianCerts⟩

theorem medianTargetCert_checked :
    medianTargetCert.Check G005.featureA 3 target half left right := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [medianTargetCert, medianCerts, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact medCert10_checked
    · exact medCert11_checked
    · exact medCert12_checked
    · exact medCert13_checked
    · exact medCert14_checked
    · exact medCert15_checked
    · exact medCert16_checked
    · exact medCert17_checked
    · exact medCert18_checked
    · exact medCert19_checked
    · exact medCert20_checked
    · exact medCert21_checked
    · exact medCert22_checked
    · exact medCert23_checked
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
    rcases hab with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases negative
      · exact ⟨medCert04, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert05, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert06, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert07, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert08, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert09, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert10, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert11, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert12, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert13, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert14, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert15, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert16, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert17, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert18, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert19, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert20, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert21, by simp [medianTargetCert, medianCerts], rfl⟩
    · cases negative
      · exact ⟨medCert22, by simp [medianTargetCert, medianCerts], rfl⟩
      · exact ⟨medCert23, by simp [medianTargetCert, medianCerts], rfl⟩
  · intro a ha b hb hab
    simp only [G005.featureA, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl
    all_goals rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals simp [medianTargetCert, medianPairs] at *

theorem majority_of_target (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ))
    (hcontains : SymbolicPolygonContains target t q.center) :
    BaselineMajorityCapture G005.featureA 3 q := by
  exact median_target_certificate_sound medianTargetCert G005.featureA 3
    target half left right medianTargetCert_checked q t ha hlt htu
    (by norm_num [half]) (by norm_num) hcontains

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.majority_of_target
