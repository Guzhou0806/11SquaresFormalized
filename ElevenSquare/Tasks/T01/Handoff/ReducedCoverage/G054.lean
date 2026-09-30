import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G054
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(45, ⟨2, by decide⟩), (203, ⟨0, by decide⟩), (483, ⟨4, by decide⟩), (503, ⟨4, by decide⟩), (519, ⟨3, by decide⟩), (522, ⟨4, by decide⟩), (523, ⟨4, by decide⟩), (536, ⟨4, by decide⟩), (591, ⟨5, by decide⟩), (642, ⟨53, by decide⟩), (645, ⟨55, by decide⟩), (648, ⟨55, by decide⟩), (788, ⟨2, by decide⟩), (808, ⟨2, by decide⟩), (824, ⟨1, by decide⟩), (827, ⟨2, by decide⟩), (828, ⟨2, by decide⟩), (840, ⟨0, by decide⟩), (892, ⟨0, by decide⟩), (940, ⟨0, by decide⟩), (943, ⟨0, by decide⟩), (946, ⟨0, by decide⟩), (1056, ⟨31, by decide⟩), (1058, ⟨35, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def part1 : List (ℕ × Group) := [(1074, ⟨20, by decide⟩), (1077, ⟨55, by decide⟩), (1078, ⟨55, by decide⟩), (1087, ⟨20, by decide⟩), (1090, ⟨55, by decide⟩), (1091, ⟨31, by decide⟩), (1097, ⟨20, by decide⟩), (1101, ⟨33, by decide⟩), (1104, ⟨55, by decide⟩), (1119, ⟨53, by decide⟩), (1122, ⟨55, by decide⟩), (1134, ⟨19, by decide⟩), (1233, ⟨20, by decide⟩), (1279, ⟨20, by decide⟩), (1321, ⟨1, by decide⟩), (1324, ⟨3, by decide⟩), (1418, ⟨35, by decide⟩), (1457, ⟨33, by decide⟩), (1460, ⟨55, by decide⟩), (1471, ⟨53, by decide⟩), (1474, ⟨55, by decide⟩), (1482, ⟨19, by decide⟩), (1509, ⟨20, by decide⟩), (1545, ⟨1, by decide⟩)]
theorem part1_valid :
    part1.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def part2 : List (ℕ × Group) := [(1547, ⟨3, by decide⟩), (1558, ⟨1, by decide⟩), (1560, ⟨3, by decide⟩), (1568, ⟨1, by decide⟩), (1590, ⟨33, by decide⟩), (1592, ⟨35, by decide⟩), (1600, ⟨19, by decide⟩), (1602, ⟨19, by decide⟩)]
theorem part2_valid :
    part2.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0 ++ part1 ++ part2
theorem keys : assignments.map Prod.fst = groupCases (⟨54, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  apply List.forall_iff_forall_mem.mpr
  intro p hp
  simp only [assignments, List.mem_append, or_assoc] at hp
  rcases hp with h | h | h
  · exact (List.forall_iff_forall_mem.mp part0_valid) p h
  · exact (List.forall_iff_forall_mem.mp part1_valid) p h
  · exact (List.forall_iff_forall_mem.mp part2_valid) p h
theorem covers : Covered (⟨54, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G054
