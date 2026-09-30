import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C24
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1708, ⟨3, by decide⟩), (1709, ⟨80, by decide⟩), (1710, ⟨3, by decide⟩), (1711, ⟨3, by decide⟩),
  (1712, ⟨3, by decide⟩), (1713, ⟨3, by decide⟩), (1714, ⟨3, by decide⟩), (1715, ⟨3, by decide⟩),
  (1717, ⟨3, by decide⟩), (1718, ⟨3, by decide⟩), (1719, ⟨3, by decide⟩), (1720, ⟨3, by decide⟩),
  (1721, ⟨3, by decide⟩), (1723, ⟨76, by decide⟩), (1724, ⟨3, by decide⟩), (1725, ⟨21, by decide⟩),
  (1726, ⟨3, by decide⟩), (1727, ⟨78, by decide⟩), (1730, ⟨3, by decide⟩), (1732, ⟨3, by decide⟩),
  (1733, ⟨50, by decide⟩), (1734, ⟨58, by decide⟩), (1735, ⟨3, by decide⟩), (1736, ⟨58, by decide⟩),
  (1737, ⟨50, by decide⟩), (1738, ⟨50, by decide⟩), (1739, ⟨50, by decide⟩), (1740, ⟨3, by decide⟩),
  (1741, ⟨3, by decide⟩), (1742, ⟨3, by decide⟩), (1743, ⟨21, by decide⟩), (1744, ⟨3, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1745, ⟨60, by decide⟩), (1746, ⟨23, by decide⟩), (1747, ⟨3, by decide⟩), (1748, ⟨9, by decide⟩),
  (1749, ⟨3, by decide⟩), (1750, ⟨27, by decide⟩), (1751, ⟨45, by decide⟩), (1752, ⟨45, by decide⟩),
  (1753, ⟨9, by decide⟩), (1754, ⟨3, by decide⟩), (1755, ⟨3, by decide⟩), (1756, ⟨45, by decide⟩),
  (1757, ⟨45, by decide⟩), (1758, ⟨9, by decide⟩), (1759, ⟨9, by decide⟩), (1760, ⟨3, by decide⟩),
  (1761, ⟨3, by decide⟩), (1762, ⟨3, by decide⟩), (1763, ⟨0, by decide⟩), (1764, ⟨3, by decide⟩),
  (1765, ⟨3, by decide⟩), (1766, ⟨3, by decide⟩), (1767, ⟨3, by decide⟩), (1768, ⟨3, by decide⟩),
  (1770, ⟨18, by decide⟩), (1771, ⟨3, by decide⟩), (1772, ⟨0, by decide⟩), (1773, ⟨3, by decide⟩),
  (1776, ⟨84, by decide⟩), (1777, ⟨3, by decide⟩), (1778, ⟨37, by decide⟩), (1779, ⟨3, by decide⟩)
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

theorem keys_match : baselineArrayChunk24.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C24
