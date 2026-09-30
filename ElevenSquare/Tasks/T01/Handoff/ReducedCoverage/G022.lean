import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G022
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def part0 : List (ℕ × Group) := [(39, ⟨1, by decide⟩), (90, ⟨4, by decide⟩), (144, ⟨3, by decide⟩), (160, ⟨5, by decide⟩), (164, ⟨3, by decide⟩), (183, ⟨3, by decide⟩), (185, ⟨3, by decide⟩), (186, ⟨3, by decide⟩), (215, ⟨0, by decide⟩), (225, ⟨36, by decide⟩), (229, ⟨36, by decide⟩), (230, ⟨3, by decide⟩), (270, ⟨3, by decide⟩), (290, ⟨3, by decide⟩), (309, ⟨3, by decide⟩), (311, ⟨3, by decide⟩), (312, ⟨3, by decide⟩), (381, ⟨3, by decide⟩), (400, ⟨3, by decide⟩), (402, ⟨3, by decide⟩), (403, ⟨3, by decide⟩), (415, ⟨3, by decide⟩), (417, ⟨3, by decide⟩), (418, ⟨3, by decide⟩)]
theorem part0_valid :
    part0.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def part1 : List (ℕ × Group) := [(429, ⟨3, by decide⟩), (430, ⟨3, by decide⟩), (431, ⟨3, by decide⟩), (477, ⟨3, by decide⟩), (497, ⟨3, by decide⟩), (516, ⟨3, by decide⟩), (518, ⟨3, by decide⟩), (519, ⟨3, by decide⟩), (587, ⟨3, by decide⟩), (606, ⟨3, by decide⟩), (608, ⟨3, by decide⟩), (609, ⟨3, by decide⟩), (621, ⟨3, by decide⟩), (623, ⟨3, by decide⟩), (624, ⟨3, by decide⟩), (635, ⟨3, by decide⟩), (636, ⟨3, by decide⟩), (637, ⟨3, by decide⟩), (665, ⟨3, by decide⟩), (684, ⟨3, by decide⟩), (686, ⟨3, by decide⟩), (687, ⟨3, by decide⟩), (699, ⟨3, by decide⟩), (701, ⟨3, by decide⟩)]
theorem part1_valid :
    part1.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def part2 : List (ℕ × Group) := [(702, ⟨3, by decide⟩), (713, ⟨3, by decide⟩), (714, ⟨3, by decide⟩), (715, ⟨0, by decide⟩), (740, ⟨3, by decide⟩), (742, ⟨3, by decide⟩), (743, ⟨3, by decide⟩), (753, ⟨3, by decide⟩), (754, ⟨3, by decide⟩), (755, ⟨3, by decide⟩), (757, ⟨3, by decide⟩), (758, ⟨3, by decide⟩), (759, ⟨3, by decide⟩), (782, ⟨1, by decide⟩), (798, ⟨36, by decide⟩), (802, ⟨1, by decide⟩), (821, ⟨1, by decide⟩), (823, ⟨1, by decide⟩), (824, ⟨1, by decide⟩), (852, ⟨0, by decide⟩), (862, ⟨36, by decide⟩), (866, ⟨21, by decide⟩), (888, ⟨36, by decide⟩), (904, ⟨0, by decide⟩)]
theorem part2_valid :
    part2.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def part3 : List (ℕ × Group) := [(907, ⟨3, by decide⟩), (909, ⟨36, by decide⟩), (910, ⟨36, by decide⟩), (914, ⟨36, by decide⟩), (918, ⟨36, by decide⟩), (921, ⟨36, by decide⟩), (923, ⟨36, by decide⟩), (924, ⟨36, by decide⟩), (934, ⟨36, by decide⟩), (935, ⟨36, by decide⟩), (936, ⟨36, by decide⟩), (946, ⟨0, by decide⟩), (950, ⟨0, by decide⟩), (960, ⟨36, by decide⟩), (979, ⟨3, by decide⟩), (981, ⟨36, by decide⟩), (982, ⟨20, by decide⟩), (993, ⟨36, by decide⟩), (995, ⟨36, by decide⟩), (996, ⟨20, by decide⟩), (1006, ⟨36, by decide⟩), (1007, ⟨20, by decide⟩), (1029, ⟨3, by decide⟩), (1031, ⟨36, by decide⟩)]
theorem part3_valid :
    part3.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def part4 : List (ℕ × Group) := [(1032, ⟨23, by decide⟩), (1041, ⟨3, by decide⟩), (1042, ⟨3, by decide⟩), (1044, ⟨36, by decide⟩), (1045, ⟨36, by decide⟩), (1052, ⟨26, by decide⟩), (1071, ⟨36, by decide⟩), (1073, ⟨36, by decide⟩), (1074, ⟨20, by decide⟩), (1084, ⟨36, by decide⟩), (1086, ⟨31, by decide⟩), (1087, ⟨20, by decide⟩), (1096, ⟨36, by decide⟩), (1097, ⟨20, by decide⟩), (1118, ⟨36, by decide⟩), (1120, ⟨36, by decide⟩), (1121, ⟨36, by decide⟩), (1129, ⟨36, by decide⟩), (1130, ⟨36, by decide⟩), (1132, ⟨36, by decide⟩), (1133, ⟨36, by decide⟩), (1139, ⟨25, by decide⟩), (1141, ⟨36, by decide⟩), (1142, ⟨20, by decide⟩)]
theorem part4_valid :
    part4.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def part5 : List (ℕ × Group) := [(1150, ⟨36, by decide⟩), (1151, ⟨20, by decide⟩), (1153, ⟨36, by decide⟩), (1154, ⟨20, by decide⟩), (1159, ⟨36, by decide⟩), (1160, ⟨19, by decide⟩)]
theorem part5_valid :
    part5.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  decide

def assignments : List (ℕ × Group) := part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5
theorem keys : assignments.map Prod.fst = groupCases (⟨22, by decide⟩ : Group) := by
  decide
theorem valid : assignments.Forall
    (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2) := by
  apply List.forall_iff_forall_mem.mpr
  intro p hp
  simp only [assignments, List.mem_append, or_assoc] at hp
  rcases hp with h | h | h | h | h | h
  · exact (List.forall_iff_forall_mem.mp part0_valid) p h
  · exact (List.forall_iff_forall_mem.mp part1_valid) p h
  · exact (List.forall_iff_forall_mem.mp part2_valid) p h
  · exact (List.forall_iff_forall_mem.mp part3_valid) p h
  · exact (List.forall_iff_forall_mem.mp part4_valid) p h
  · exact (List.forall_iff_forall_mem.mp part5_valid) p h
theorem covers : Covered (⟨22, by decide⟩ : Group) :=
  covered_of_assignments _ assignments keys valid
end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G022
