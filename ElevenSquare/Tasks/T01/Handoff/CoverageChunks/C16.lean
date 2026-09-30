import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C16
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1081, ⟨36, by decide⟩), (1082, ⟨24, by decide⟩), (1084, ⟨22, by decide⟩), (1085, ⟨32, by decide⟩),
  (1086, ⟨24, by decide⟩), (1087, ⟨54, by decide⟩), (1088, ⟨35, by decide⟩), (1089, ⟨52, by decide⟩),
  (1090, ⟨54, by decide⟩), (1091, ⟨35, by decide⟩), (1092, ⟨24, by decide⟩), (1093, ⟨24, by decide⟩),
  (1094, ⟨36, by decide⟩), (1095, ⟨0, by decide⟩), (1096, ⟨50, by decide⟩), (1097, ⟨54, by decide⟩),
  (1098, ⟨55, by decide⟩), (1099, ⟨33, by decide⟩), (1100, ⟨28, by decide⟩), (1101, ⟨33, by decide⟩),
  (1102, ⟨26, by decide⟩), (1103, ⟨26, by decide⟩), (1104, ⟨51, by decide⟩), (1105, ⟨35, by decide⟩),
  (1106, ⟨35, by decide⟩), (1113, ⟨53, by decide⟩), (1116, ⟨55, by decide⟩), (1117, ⟨19, by decide⟩),
  (1118, ⟨28, by decide⟩), (1119, ⟨53, by decide⟩), (1120, ⟨55, by decide⟩), (1121, ⟨22, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1122, ⟨51, by decide⟩), (1123, ⟨55, by decide⟩), (1126, ⟨36, by decide⟩), (1127, ⟨36, by decide⟩),
  (1129, ⟨22, by decide⟩), (1130, ⟨22, by decide⟩), (1131, ⟨53, by decide⟩), (1132, ⟨22, by decide⟩),
  (1133, ⟨22, by decide⟩), (1134, ⟨51, by decide⟩), (1135, ⟨28, by decide⟩), (1136, ⟨28, by decide⟩),
  (1137, ⟨45, by decide⟩), (1138, ⟨19, by decide⟩), (1139, ⟨25, by decide⟩), (1140, ⟨0, by decide⟩),
  (1141, ⟨22, by decide⟩), (1142, ⟨20, by decide⟩), (1144, ⟨11, by decide⟩), (1146, ⟨45, by decide⟩),
  (1147, ⟨45, by decide⟩), (1148, ⟨36, by decide⟩), (1149, ⟨0, by decide⟩), (1150, ⟨22, by decide⟩),
  (1151, ⟨20, by decide⟩), (1152, ⟨0, by decide⟩), (1153, ⟨22, by decide⟩), (1154, ⟨20, by decide⟩),
  (1155, ⟨19, by decide⟩), (1157, ⟨19, by decide⟩), (1158, ⟨19, by decide⟩), (1159, ⟨22, by decide⟩)
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

theorem keys_match : baselineArrayChunk16.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C16
