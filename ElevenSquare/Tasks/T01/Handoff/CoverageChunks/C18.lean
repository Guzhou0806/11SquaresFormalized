import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C18
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1224, ⟨19, by decide⟩), (1225, ⟨19, by decide⟩), (1226, ⟨3, by decide⟩), (1227, ⟨55, by decide⟩),
  (1228, ⟨33, by decide⟩), (1229, ⟨18, by decide⟩), (1230, ⟨55, by decide⟩), (1231, ⟨3, by decide⟩),
  (1232, ⟨48, by decide⟩), (1233, ⟨54, by decide⟩), (1234, ⟨55, by decide⟩), (1236, ⟨20, by decide⟩),
  (1237, ⟨3, by decide⟩), (1238, ⟨18, by decide⟩), (1239, ⟨20, by decide⟩), (1240, ⟨18, by decide⟩),
  (1241, ⟨18, by decide⟩), (1242, ⟨20, by decide⟩), (1243, ⟨20, by decide⟩), (1244, ⟨3, by decide⟩),
  (1245, ⟨3, by decide⟩), (1246, ⟨3, by decide⟩), (1247, ⟨3, by decide⟩), (1250, ⟨39, by decide⟩),
  (1251, ⟨3, by decide⟩), (1252, ⟨3, by decide⟩), (1253, ⟨3, by decide⟩), (1254, ⟨3, by decide⟩),
  (1255, ⟨3, by decide⟩), (1256, ⟨3, by decide⟩), (1260, ⟨53, by decide⟩), (1263, ⟨42, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1272, ⟨3, by decide⟩), (1273, ⟨55, by decide⟩), (1274, ⟨23, by decide⟩), (1275, ⟨3, by decide⟩),
  (1276, ⟨55, by decide⟩), (1277, ⟨3, by decide⟩), (1278, ⟨44, by decide⟩), (1279, ⟨54, by decide⟩),
  (1280, ⟨55, by decide⟩), (1282, ⟨20, by decide⟩), (1283, ⟨3, by decide⟩), (1284, ⟨3, by decide⟩),
  (1285, ⟨20, by decide⟩), (1286, ⟨20, by decide⟩), (1287, ⟨3, by decide⟩), (1288, ⟨20, by decide⟩),
  (1289, ⟨20, by decide⟩), (1290, ⟨3, by decide⟩), (1291, ⟨3, by decide⟩), (1292, ⟨3, by decide⟩),
  (1293, ⟨3, by decide⟩), (1294, ⟨41, by decide⟩), (1295, ⟨3, by decide⟩), (1296, ⟨3, by decide⟩),
  (1297, ⟨3, by decide⟩), (1298, ⟨3, by decide⟩), (1299, ⟨3, by decide⟩), (1300, ⟨3, by decide⟩),
  (1301, ⟨3, by decide⟩), (1302, ⟨3, by decide⟩), (1304, ⟨39, by decide⟩), (1305, ⟨3, by decide⟩)
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

theorem keys_match : baselineArrayChunk18.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C18
