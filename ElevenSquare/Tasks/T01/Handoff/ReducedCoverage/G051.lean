import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G051
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(45, ⟨2, by decide⟩), (483, ⟨4, by decide⟩), (503, ⟨4, by decide⟩), (519, ⟨3, by decide⟩), (522, ⟨4, by decide⟩), (523, ⟨4, by decide⟩), (645, ⟨55, by decide⟩), (943, ⟨0, by decide⟩), (1104, ⟨55, by decide⟩), (1122, ⟨55, by decide⟩), (1134, ⟨19, by decide⟩), (1324, ⟨3, by decide⟩), (1460, ⟨55, by decide⟩), (1474, ⟨55, by decide⟩), (1482, ⟨19, by decide⟩), (1547, ⟨3, by decide⟩), (1560, ⟨3, by decide⟩), (1568, ⟨1, by decide⟩), (1592, ⟨35, by decide⟩), (1600, ⟨19, by decide⟩), (1602, ⟨19, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0
theorem keys : assignments.map Prod.fst = groupCases (⟨51, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  exact part0_valid
theorem covers : Covered (⟨51, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G051
