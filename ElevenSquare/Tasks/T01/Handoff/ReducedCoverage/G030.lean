import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G030
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(531, ⟨4, by decide⟩), (1537, ⟨52, by decide⟩), (1663, ⟨10, by decide⟩), (1802, ⟨58, by decide⟩), (1834, ⟨19, by decide⟩), (1836, ⟨56, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0
theorem keys : assignments.map Prod.fst = groupCases (⟨30, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  exact part0_valid
theorem covers : Covered (⟨30, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G030
