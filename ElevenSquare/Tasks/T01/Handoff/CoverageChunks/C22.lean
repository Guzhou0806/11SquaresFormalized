import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C22
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1548, ⟨55, by decide⟩), (1549, ⟨20, by decide⟩), (1550, ⟨20, by decide⟩), (1551, ⟨3, by decide⟩),
  (1552, ⟨3, by decide⟩), (1553, ⟨42, by decide⟩), (1555, ⟨55, by decide⟩), (1556, ⟨39, by decide⟩),
  (1557, ⟨15, by decide⟩), (1558, ⟨23, by decide⟩), (1559, ⟨55, by decide⟩), (1560, ⟨51, by decide⟩),
  (1561, ⟨55, by decide⟩), (1562, ⟨20, by decide⟩), (1563, ⟨20, by decide⟩), (1564, ⟨3, by decide⟩),
  (1565, ⟨3, by decide⟩), (1566, ⟨39, by decide⟩), (1568, ⟨51, by decide⟩), (1569, ⟨15, by decide⟩),
  (1570, ⟨3, by decide⟩), (1571, ⟨18, by decide⟩), (1572, ⟨25, by decide⟩), (1573, ⟨46, by decide⟩),
  (1575, ⟨3, by decide⟩), (1576, ⟨3, by decide⟩), (1577, ⟨3, by decide⟩), (1578, ⟨3, by decide⟩),
  (1579, ⟨46, by decide⟩), (1580, ⟨3, by decide⟩), (1581, ⟨18, by decide⟩), (1583, ⟨1, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1584, ⟨3, by decide⟩), (1585, ⟨23, by decide⟩), (1586, ⟨3, by decide⟩), (1587, ⟨55, by decide⟩),
  (1588, ⟨33, by decide⟩), (1589, ⟨26, by decide⟩), (1590, ⟨29, by decide⟩), (1591, ⟨26, by decide⟩),
  (1592, ⟨51, by decide⟩), (1593, ⟨52, by decide⟩), (1596, ⟨57, by decide⟩), (1598, ⟨32, by decide⟩),
  (1599, ⟨52, by decide⟩), (1600, ⟨51, by decide⟩), (1601, ⟨49, by decide⟩), (1602, ⟨51, by decide⟩),
  (1603, ⟨49, by decide⟩), (1604, ⟨19, by decide⟩), (1605, ⟨25, by decide⟩), (1606, ⟨25, by decide⟩),
  (1607, ⟨25, by decide⟩), (1608, ⟨16, by decide⟩), (1609, ⟨25, by decide⟩), (1610, ⟨52, by decide⟩),
  (1611, ⟨25, by decide⟩), (1612, ⟨11, by decide⟩), (1613, ⟨25, by decide⟩), (1614, ⟨25, by decide⟩),
  (1615, ⟨9, by decide⟩), (1616, ⟨25, by decide⟩), (1617, ⟨25, by decide⟩), (1618, ⟨11, by decide⟩)
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

theorem keys_match : baselineArrayChunk22.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C22
