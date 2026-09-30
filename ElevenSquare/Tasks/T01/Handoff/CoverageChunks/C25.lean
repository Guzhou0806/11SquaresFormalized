import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C25
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1780, ⟨19, by decide⟩), (1781, ⟨3, by decide⟩), (1782, ⟨38, by decide⟩), (1784, ⟨38, by decide⟩),
  (1785, ⟨3, by decide⟩), (1786, ⟨3, by decide⟩), (1787, ⟨3, by decide⟩), (1788, ⟨21, by decide⟩),
  (1789, ⟨3, by decide⟩), (1790, ⟨23, by decide⟩), (1791, ⟨3, by decide⟩), (1792, ⟨23, by decide⟩),
  (1793, ⟨3, by decide⟩), (1794, ⟨3, by decide⟩), (1795, ⟨3, by decide⟩), (1796, ⟨3, by decide⟩),
  (1797, ⟨3, by decide⟩), (1798, ⟨21, by decide⟩), (1799, ⟨1, by decide⟩), (1800, ⟨74, by decide⟩),
  (1801, ⟨11, by decide⟩), (1802, ⟨30, by decide⟩), (1803, ⟨14, by decide⟩), (1804, ⟨27, by decide⟩),
  (1806, ⟨27, by decide⟩), (1807, ⟨11, by decide⟩), (1808, ⟨11, by decide⟩), (1809, ⟨27, by decide⟩),
  (1811, ⟨3, by decide⟩), (1812, ⟨11, by decide⟩), (1813, ⟨11, by decide⟩), (1814, ⟨27, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1815, ⟨27, by decide⟩), (1816, ⟨64, by decide⟩), (1817, ⟨44, by decide⟩), (1818, ⟨3, by decide⟩),
  (1819, ⟨0, by decide⟩), (1820, ⟨3, by decide⟩), (1825, ⟨48, by decide⟩), (1826, ⟨3, by decide⟩),
  (1827, ⟨32, by decide⟩), (1828, ⟨3, by decide⟩), (1829, ⟨35, by decide⟩), (1830, ⟨56, by decide⟩),
  (1832, ⟨37, by decide⟩), (1833, ⟨75, by decide⟩), (1834, ⟨30, by decide⟩), (1835, ⟨14, by decide⟩),
  (1836, ⟨30, by decide⟩), (1837, ⟨14, by decide⟩), (1838, ⟨56, by decide⟩), (1841, ⟨66, by decide⟩),
  (1843, ⟨58, by decide⟩), (1844, ⟨3, by decide⟩), (1845, ⟨73, by decide⟩), (1846, ⟨3, by decide⟩),
  (1851, ⟨58, by decide⟩), (1852, ⟨9, by decide⟩), (1853, ⟨19, by decide⟩), (1854, ⟨27, by decide⟩),
  (1855, ⟨0, by decide⟩), (1856, ⟨3, by decide⟩), (1857, ⟨9, by decide⟩), (1858, ⟨9, by decide⟩)
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

theorem keys_match : baselineArrayChunk25.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C25
