import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C17
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1160, ⟨19, by decide⟩), (1161, ⟨25, by decide⟩), (1162, ⟨25, by decide⟩), (1163, ⟨25, by decide⟩),
  (1164, ⟨25, by decide⟩), (1165, ⟨25, by decide⟩), (1166, ⟨25, by decide⟩), (1167, ⟨25, by decide⟩),
  (1168, ⟨25, by decide⟩), (1169, ⟨18, by decide⟩), (1170, ⟨27, by decide⟩), (1171, ⟨25, by decide⟩),
  (1172, ⟨25, by decide⟩), (1173, ⟨25, by decide⟩), (1174, ⟨25, by decide⟩), (1175, ⟨25, by decide⟩),
  (1176, ⟨19, by decide⟩), (1177, ⟨19, by decide⟩), (1178, ⟨15, by decide⟩), (1179, ⟨10, by decide⟩),
  (1180, ⟨19, by decide⟩), (1181, ⟨19, by decide⟩), (1182, ⟨19, by decide⟩), (1183, ⟨47, by decide⟩),
  (1184, ⟨19, by decide⟩), (1185, ⟨49, by decide⟩), (1186, ⟨19, by decide⟩), (1187, ⟨19, by decide⟩),
  (1188, ⟨23, by decide⟩), (1189, ⟨19, by decide⟩), (1190, ⟨23, by decide⟩), (1191, ⟨23, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1192, ⟨19, by decide⟩), (1193, ⟨19, by decide⟩), (1194, ⟨19, by decide⟩), (1195, ⟨19, by decide⟩),
  (1196, ⟨19, by decide⟩), (1197, ⟨15, by decide⟩), (1198, ⟨10, by decide⟩), (1199, ⟨19, by decide⟩),
  (1200, ⟨19, by decide⟩), (1201, ⟨19, by decide⟩), (1202, ⟨47, by decide⟩), (1203, ⟨19, by decide⟩),
  (1204, ⟨26, by decide⟩), (1205, ⟨19, by decide⟩), (1206, ⟨19, by decide⟩), (1207, ⟨19, by decide⟩),
  (1208, ⟨19, by decide⟩), (1209, ⟨19, by decide⟩), (1210, ⟨19, by decide⟩), (1211, ⟨19, by decide⟩),
  (1212, ⟨19, by decide⟩), (1213, ⟨19, by decide⟩), (1214, ⟨19, by decide⟩), (1215, ⟨15, by decide⟩),
  (1216, ⟨10, by decide⟩), (1217, ⟨15, by decide⟩), (1218, ⟨10, by decide⟩), (1219, ⟨15, by decide⟩),
  (1220, ⟨47, by decide⟩), (1221, ⟨58, by decide⟩), (1222, ⟨49, by decide⟩), (1223, ⟨19, by decide⟩)
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

theorem keys_match : baselineArrayChunk17.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C17
