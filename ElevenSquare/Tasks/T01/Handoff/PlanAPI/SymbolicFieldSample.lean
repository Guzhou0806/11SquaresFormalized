import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldRow
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.Bridge

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldSample
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending
noncomputable section

def point : QPoint :=
  (498020679/500000000, 997648353/1000000000)

def cert : SymbolicFieldRowCertificate where
  source := source
  targets := [.median target00, .blocker target01 point (49999/100000)]
  cover := node000

theorem cert_checked : cert.Check 4 (1/256) (1/128) := by
  refine ⟨source_eq, ?_, ?_⟩
  · simpa [cert, SymbolicFieldTarget.polygon, targets] using cover_checked
  · intro target htarget
    simp only [cert, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at htarget
    rcases htarget with rfl | rfl
    · trivial
    · refine ⟨by norm_num, by norm_num, ?_⟩
      intro f hf
      norm_num [symbolicPointTarget, symbolicPointFacet,
        symbolicPointNormal, symbolicPointBound, point,
        List.finRange] at hf
      rcases hf with rfl | rfl | rfl | rfl
      all_goals norm_num [target01]

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldSample

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldSample.cert_checked
