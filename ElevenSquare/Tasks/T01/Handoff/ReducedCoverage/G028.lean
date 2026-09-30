import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G028
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(641, ⟨47, by decide⟩), (939, ⟨3, by decide⟩), (1100, ⟨26, by decide⟩), (1118, ⟨36, by decide⟩), (1135, ⟨47, by decide⟩), (1136, ⟨19, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0
theorem keys : assignments.map Prod.fst = groupCases (⟨28, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  exact part0_valid
theorem covers : Covered (⟨28, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G028
