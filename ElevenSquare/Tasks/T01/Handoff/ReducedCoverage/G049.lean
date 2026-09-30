import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G049
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(45, ⟨2, by decide⟩), (641, ⟨47, by decide⟩), (939, ⟨3, by decide⟩), (1100, ⟨26, by decide⟩), (1118, ⟨36, by decide⟩), (1135, ⟨47, by decide⟩), (1136, ⟨19, by decide⟩), (1185, ⟨19, by decide⟩), (1204, ⟨19, by decide⟩), (1219, ⟨3, by decide⟩), (1222, ⟨19, by decide⟩), (1320, ⟨3, by decide⟩), (1456, ⟨26, by decide⟩), (1470, ⟨3, by decide⟩), (1483, ⟨55, by decide⟩), (1544, ⟨3, by decide⟩), (1557, ⟨3, by decide⟩), (1569, ⟨3, by decide⟩), (1589, ⟨25, by decide⟩), (1601, ⟨26, by decide⟩), (1603, ⟨55, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0
theorem keys : assignments.map Prod.fst = groupCases (⟨49, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  exact part0_valid
theorem covers : Covered (⟨49, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G049
