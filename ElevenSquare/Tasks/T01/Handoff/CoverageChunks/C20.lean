import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C20
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1387, ⟨3, by decide⟩), (1388, ⟨3, by decide⟩), (1389, ⟨3, by decide⟩), (1390, ⟨3, by decide⟩),
  (1391, ⟨3, by decide⟩), (1392, ⟨21, by decide⟩), (1394, ⟨3, by decide⟩), (1395, ⟨23, by decide⟩),
  (1396, ⟨3, by decide⟩), (1397, ⟨23, by decide⟩), (1398, ⟨3, by decide⟩), (1399, ⟨23, by decide⟩),
  (1400, ⟨3, by decide⟩), (1401, ⟨3, by decide⟩), (1402, ⟨3, by decide⟩), (1403, ⟨3, by decide⟩),
  (1404, ⟨3, by decide⟩), (1405, ⟨3, by decide⟩), (1406, ⟨3, by decide⟩), (1407, ⟨21, by decide⟩),
  (1408, ⟨3, by decide⟩), (1409, ⟨1, by decide⟩), (1410, ⟨3, by decide⟩), (1412, ⟨55, by decide⟩),
  (1413, ⟨33, by decide⟩), (1414, ⟨26, by decide⟩), (1415, ⟨27, by decide⟩), (1418, ⟨35, by decide⟩),
  (1419, ⟨55, by decide⟩), (1421, ⟨27, by decide⟩), (1423, ⟨3, by decide⟩), (1425, ⟨3, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1426, ⟨3, by decide⟩), (1427, ⟨27, by decide⟩), (1428, ⟨27, by decide⟩), (1431, ⟨44, by decide⟩),
  (1432, ⟨3, by decide⟩), (1434, ⟨3, by decide⟩), (1435, ⟨3, by decide⟩), (1440, ⟨3, by decide⟩),
  (1442, ⟨48, by decide⟩), (1443, ⟨3, by decide⟩), (1444, ⟨32, by decide⟩), (1445, ⟨3, by decide⟩),
  (1446, ⟨3, by decide⟩), (1447, ⟨35, by decide⟩), (1448, ⟨52, by decide⟩), (1451, ⟨3, by decide⟩),
  (1452, ⟨37, by decide⟩), (1453, ⟨3, by decide⟩), (1454, ⟨55, by decide⟩), (1455, ⟨33, by decide⟩),
  (1456, ⟨26, by decide⟩), (1457, ⟨33, by decide⟩), (1458, ⟨26, by decide⟩), (1459, ⟨26, by decide⟩),
  (1460, ⟨51, by decide⟩), (1461, ⟨55, by decide⟩), (1466, ⟨53, by decide⟩), (1468, ⟨55, by decide⟩),
  (1469, ⟨19, by decide⟩), (1470, ⟨49, by decide⟩), (1471, ⟨53, by decide⟩), (1472, ⟨55, by decide⟩)
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

theorem keys_match : baselineArrayChunk20.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C20
