import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C23
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1619, ⟨11, by decide⟩), (1620, ⟨3, by decide⟩), (1622, ⟨15, by decide⟩), (1623, ⟨3, by decide⟩),
  (1624, ⟨3, by decide⟩), (1625, ⟨3, by decide⟩), (1626, ⟨3, by decide⟩), (1627, ⟨47, by decide⟩),
  (1629, ⟨3, by decide⟩), (1630, ⟨3, by decide⟩), (1631, ⟨3, by decide⟩), (1633, ⟨3, by decide⟩),
  (1634, ⟨3, by decide⟩), (1635, ⟨3, by decide⟩), (1638, ⟨15, by decide⟩), (1639, ⟨3, by decide⟩),
  (1643, ⟨47, by decide⟩), (1647, ⟨3, by decide⟩), (1649, ⟨3, by decide⟩), (1652, ⟨65, by decide⟩),
  (1653, ⟨15, by decide⟩), (1654, ⟨3, by decide⟩), (1655, ⟨47, by decide⟩), (1656, ⟨3, by decide⟩),
  (1657, ⟨47, by decide⟩), (1658, ⟨69, by decide⟩), (1660, ⟨3, by decide⟩), (1661, ⟨3, by decide⟩),
  (1662, ⟨16, by decide⟩), (1663, ⟨30, by decide⟩), (1664, ⟨14, by decide⟩), (1665, ⟨16, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1666, ⟨3, by decide⟩), (1667, ⟨52, by decide⟩), (1668, ⟨16, by decide⟩), (1669, ⟨16, by decide⟩),
  (1670, ⟨3, by decide⟩), (1671, ⟨3, by decide⟩), (1672, ⟨3, by decide⟩), (1675, ⟨3, by decide⟩),
  (1676, ⟨3, by decide⟩), (1677, ⟨3, by decide⟩), (1678, ⟨3, by decide⟩), (1679, ⟨3, by decide⟩),
  (1681, ⟨82, by decide⟩), (1682, ⟨3, by decide⟩), (1683, ⟨3, by decide⟩), (1684, ⟨3, by decide⟩),
  (1685, ⟨3, by decide⟩), (1687, ⟨63, by decide⟩), (1689, ⟨21, by decide⟩), (1690, ⟨79, by decide⟩),
  (1692, ⟨81, by decide⟩), (1697, ⟨3, by decide⟩), (1698, ⟨62, by decide⟩), (1699, ⟨58, by decide⟩),
  (1700, ⟨3, by decide⟩), (1701, ⟨50, by decide⟩), (1702, ⟨3, by decide⟩), (1703, ⟨3, by decide⟩),
  (1704, ⟨50, by decide⟩), (1705, ⟨59, by decide⟩), (1706, ⟨3, by decide⟩), (1707, ⟨3, by decide⟩)
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

theorem keys_match : baselineArrayChunk23.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C23
