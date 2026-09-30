import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G024
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(27, ⟨1, by decide⟩), (465, ⟨4, by decide⟩), (495, ⟨4, by decide⟩), (504, ⟨4, by decide⟩), (507, ⟨4, by decide⟩), (508, ⟨3, by decide⟩), (770, ⟨0, by decide⟩), (800, ⟨1, by decide⟩), (809, ⟨1, by decide⟩), (812, ⟨1, by decide⟩), (813, ⟨1, by decide⟩), (1017, ⟨31, by decide⟩), (1050, ⟨31, by decide⟩), (1059, ⟨31, by decide⟩), (1062, ⟨31, by decide⟩), (1063, ⟨31, by decide⟩), (1082, ⟨31, by decide⟩), (1085, ⟨0, by decide⟩), (1086, ⟨31, by decide⟩), (1092, ⟨31, by decide⟩), (1093, ⟨31, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0
theorem keys : assignments.map Prod.fst = groupCases (⟨24, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  exact part0_valid
theorem covers : Covered (⟨24, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G024
