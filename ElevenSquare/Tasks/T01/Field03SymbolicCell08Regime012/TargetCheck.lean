import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.Data
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.Blockers
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldRow

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def blockPoint01 : QPoint := ((124716977/125000000), (720292019/250000000))
def blockPoint02 : QPoint := ((106782017/125000000), (720292019/250000000))

def rowCertificate : SymbolicFieldRowCertificate where
  source := source
  targets := [.median target00, .blocker target01 blockPoint01 (49999/100000), .blocker target02 blockPoint02 (49999/100000)]
  cover := node000

theorem row_blockerPoints_eq : rowCertificate.blockerPoints = blockerPoints := by
  rfl

theorem row_targetPolygons_eq :
    rowCertificate.targets.map SymbolicFieldTarget.polygon = targets := by
  rfl

theorem row_targets_checked :
    ∀ target ∈ rowCertificate.targets, target.Check := by
  intro target htarget
  simp only [rowCertificate, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at htarget
  rcases htarget with rfl | rfl | rfl
  · trivial
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro f hf
    norm_num [symbolicPointTarget, symbolicPointFacet,
      symbolicPointNormal, symbolicPointBound,
      blockPoint01, List.finRange] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals norm_num [target01]
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro f hf
    norm_num [symbolicPointTarget, symbolicPointFacet,
      symbolicPointNormal, symbolicPointBound,
      blockPoint02, List.finRange] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals norm_num [target02]

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.row_targets_checked
