import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G032
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(60, ⟨4, by decide⟩), (768, ⟨2, by decide⟩), (836, ⟨21, by decide⟩), (839, ⟨3, by decide⟩), (841, ⟨0, by decide⟩), (842, ⟨35, by decide⟩), (1085, ⟨0, by decide⟩), (1444, ⟨35, by decide⟩), (1533, ⟨7, by decide⟩), (1590, ⟨33, by decide⟩), (1598, ⟨35, by decide⟩), (1827, ⟨0, by decide⟩), (1888, ⟨0, by decide⟩), (1923, ⟨0, by decide⟩), (1927, ⟨0, by decide⟩), (1953, ⟨15, by decide⟩), (1983, ⟨35, by decide⟩), (1987, ⟨35, by decide⟩), (1993, ⟨1, by decide⟩), (1997, ⟨18, by decide⟩), (2001, ⟨19, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0
theorem keys : assignments.map Prod.fst = groupCases (⟨32, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  exact part0_valid
theorem covers : Covered (⟨32, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G032
