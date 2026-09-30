import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C21
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1473, ⟨3, by decide⟩), (1474, ⟨51, by decide⟩), (1475, ⟨55, by decide⟩), (1477, ⟨3, by decide⟩),
  (1479, ⟨3, by decide⟩), (1480, ⟨53, by decide⟩), (1481, ⟨3, by decide⟩), (1482, ⟨51, by decide⟩),
  (1483, ⟨49, by decide⟩), (1485, ⟨19, by decide⟩), (1486, ⟨25, by decide⟩), (1488, ⟨3, by decide⟩),
  (1489, ⟨3, by decide⟩), (1493, ⟨3, by decide⟩), (1494, ⟨37, by decide⟩), (1495, ⟨3, by decide⟩),
  (1496, ⟨37, by decide⟩), (1497, ⟨3, by decide⟩), (1498, ⟨19, by decide⟩), (1500, ⟨19, by decide⟩),
  (1501, ⟨3, by decide⟩), (1502, ⟨3, by decide⟩), (1503, ⟨12, by decide⟩), (1504, ⟨33, by decide⟩),
  (1505, ⟨26, by decide⟩), (1506, ⟨20, by decide⟩), (1507, ⟨3, by decide⟩), (1508, ⟨3, by decide⟩),
  (1509, ⟨35, by decide⟩), (1510, ⟨20, by decide⟩), (1511, ⟨26, by decide⟩), (1512, ⟨20, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1513, ⟨3, by decide⟩), (1514, ⟨23, by decide⟩), (1515, ⟨20, by decide⟩), (1516, ⟨23, by decide⟩),
  (1517, ⟨23, by decide⟩), (1518, ⟨20, by decide⟩), (1519, ⟨20, by decide⟩), (1520, ⟨3, by decide⟩),
  (1521, ⟨3, by decide⟩), (1522, ⟨10, by decide⟩), (1523, ⟨7, by decide⟩), (1524, ⟨10, by decide⟩),
  (1525, ⟨10, by decide⟩), (1526, ⟨3, by decide⟩), (1527, ⟨58, by decide⟩), (1528, ⟨3, by decide⟩),
  (1529, ⟨23, by decide⟩), (1531, ⟨39, by decide⟩), (1532, ⟨10, by decide⟩), (1533, ⟨32, by decide⟩),
  (1534, ⟨10, by decide⟩), (1535, ⟨26, by decide⟩), (1536, ⟨42, by decide⟩), (1537, ⟨14, by decide⟩),
  (1540, ⟨7, by decide⟩), (1541, ⟨58, by decide⟩), (1542, ⟨55, by decide⟩), (1543, ⟨33, by decide⟩),
  (1544, ⟨15, by decide⟩), (1545, ⟨33, by decide⟩), (1546, ⟨26, by decide⟩), (1547, ⟨42, by decide⟩)
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

theorem keys_match : baselineArrayChunk21.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C21
