import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G017
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(114, ⟨4, by decide⟩), (184, ⟨5, by decide⟩), (219, ⟨40, by decide⟩), (234, ⟨6, by decide⟩), (246, ⟨40, by decide⟩), (249, ⟨40, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0
theorem keys : assignments.map Prod.fst = groupCases (⟨17, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  exact part0_valid
theorem covers : Covered (⟨17, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G017
