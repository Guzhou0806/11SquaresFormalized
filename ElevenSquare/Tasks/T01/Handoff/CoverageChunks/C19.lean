import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C19
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1306, ⟨53, by decide⟩), (1307, ⟨3, by decide⟩), (1308, ⟨3, by decide⟩), (1309, ⟨43, by decide⟩),
  (1313, ⟨3, by decide⟩), (1314, ⟨3, by decide⟩), (1316, ⟨3, by decide⟩), (1317, ⟨3, by decide⟩),
  (1318, ⟨55, by decide⟩), (1319, ⟨10, by decide⟩), (1320, ⟨15, by decide⟩), (1321, ⟨10, by decide⟩),
  (1322, ⟨55, by decide⟩), (1323, ⟨10, by decide⟩), (1324, ⟨51, by decide⟩), (1325, ⟨55, by decide⟩),
  (1326, ⟨3, by decide⟩), (1327, ⟨20, by decide⟩), (1328, ⟨20, by decide⟩), (1329, ⟨3, by decide⟩),
  (1330, ⟨3, by decide⟩), (1331, ⟨3, by decide⟩), (1332, ⟨43, by decide⟩), (1334, ⟨3, by decide⟩),
  (1336, ⟨23, by decide⟩), (1337, ⟨3, by decide⟩), (1338, ⟨3, by decide⟩), (1339, ⟨3, by decide⟩),
  (1340, ⟨3, by decide⟩), (1344, ⟨3, by decide⟩), (1345, ⟨3, by decide⟩), (1346, ⟨3, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1348, ⟨3, by decide⟩), (1349, ⟨3, by decide⟩), (1350, ⟨3, by decide⟩), (1351, ⟨3, by decide⟩),
  (1352, ⟨3, by decide⟩), (1353, ⟨3, by decide⟩), (1354, ⟨3, by decide⟩), (1355, ⟨3, by decide⟩),
  (1356, ⟨46, by decide⟩), (1357, ⟨3, by decide⟩), (1358, ⟨3, by decide⟩), (1359, ⟨3, by decide⟩),
  (1360, ⟨3, by decide⟩), (1361, ⟨3, by decide⟩), (1362, ⟨3, by decide⟩), (1363, ⟨3, by decide⟩),
  (1364, ⟨3, by decide⟩), (1366, ⟨18, by decide⟩), (1367, ⟨3, by decide⟩), (1368, ⟨46, by decide⟩),
  (1369, ⟨3, by decide⟩), (1370, ⟨3, by decide⟩), (1375, ⟨3, by decide⟩), (1376, ⟨3, by decide⟩),
  (1377, ⟨46, by decide⟩), (1378, ⟨3, by decide⟩), (1379, ⟨3, by decide⟩), (1380, ⟨19, by decide⟩),
  (1381, ⟨3, by decide⟩), (1382, ⟨1, by decide⟩), (1385, ⟨3, by decide⟩), (1386, ⟨3, by decide⟩)
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

theorem keys_match : baselineArrayChunk19.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C19
