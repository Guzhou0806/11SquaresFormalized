import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C15
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1004, ⟨36, by decide⟩), (1005, ⟨46, by decide⟩), (1006, ⟨22, by decide⟩), (1007, ⟨20, by decide⟩),
  (1008, ⟨3, by decide⟩), (1009, ⟨19, by decide⟩), (1010, ⟨3, by decide⟩), (1011, ⟨38, by decide⟩),
  (1014, ⟨38, by decide⟩), (1015, ⟨3, by decide⟩), (1016, ⟨3, by decide⟩), (1017, ⟨24, by decide⟩),
  (1018, ⟨3, by decide⟩), (1019, ⟨3, by decide⟩), (1020, ⟨3, by decide⟩), (1021, ⟨3, by decide⟩),
  (1022, ⟨3, by decide⟩), (1023, ⟨3, by decide⟩), (1024, ⟨21, by decide⟩), (1027, ⟨3, by decide⟩),
  (1028, ⟨23, by decide⟩), (1029, ⟨22, by decide⟩), (1030, ⟨23, by decide⟩), (1031, ⟨22, by decide⟩),
  (1032, ⟨23, by decide⟩), (1033, ⟨3, by decide⟩), (1034, ⟨3, by decide⟩), (1035, ⟨3, by decide⟩),
  (1036, ⟨36, by decide⟩), (1037, ⟨3, by decide⟩), (1038, ⟨36, by decide⟩), (1039, ⟨36, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1040, ⟨3, by decide⟩), (1041, ⟨22, by decide⟩), (1042, ⟨22, by decide⟩), (1043, ⟨21, by decide⟩),
  (1044, ⟨22, by decide⟩), (1045, ⟨22, by decide⟩), (1046, ⟨1, by decide⟩), (1047, ⟨3, by decide⟩),
  (1048, ⟨19, by decide⟩), (1050, ⟨24, by decide⟩), (1051, ⟨33, by decide⟩), (1052, ⟨26, by decide⟩),
  (1053, ⟨31, by decide⟩), (1055, ⟨35, by decide⟩), (1056, ⟨35, by decide⟩), (1057, ⟨35, by decide⟩),
  (1058, ⟨35, by decide⟩), (1059, ⟨45, by decide⟩), (1061, ⟨36, by decide⟩), (1062, ⟨24, by decide⟩),
  (1063, ⟨24, by decide⟩), (1064, ⟨36, by decide⟩), (1065, ⟨31, by decide⟩), (1066, ⟨31, by decide⟩),
  (1068, ⟨31, by decide⟩), (1071, ⟨22, by decide⟩), (1072, ⟨0, by decide⟩), (1073, ⟨22, by decide⟩),
  (1074, ⟨54, by decide⟩), (1077, ⟨54, by decide⟩), (1078, ⟨54, by decide⟩), (1080, ⟨36, by decide⟩)
]
theorem part1_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part1 := by decide

def assignments : List (ℕ × Group) := part0 ++ part1
theorem valid : List.Forall (fun p => p.1 ∈ groupCases p.2) assignments := by
  apply List.forall_iff_forall_mem.mpr
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact (List.forall_iff_forall_mem.mp part0_valid) p h
  · exact (List.forall_iff_forall_mem.mp part1_valid) p h

theorem keys_match : baselineArrayChunk15.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C15
