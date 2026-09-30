import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C26
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1859, ⟨37, by decide⟩), (1860, ⟨37, by decide⟩), (1861, ⟨19, by decide⟩), (1862, ⟨19, by decide⟩),
  (1863, ⟨3, by decide⟩), (1865, ⟨12, by decide⟩), (1867, ⟨3, by decide⟩), (1868, ⟨3, by decide⟩),
  (1869, ⟨3, by decide⟩), (1870, ⟨38, by decide⟩), (1872, ⟨45, by decide⟩), (1873, ⟨3, by decide⟩),
  (1874, ⟨3, by decide⟩), (1876, ⟨85, by decide⟩), (1877, ⟨3, by decide⟩), (1878, ⟨3, by decide⟩),
  (1879, ⟨3, by decide⟩), (1880, ⟨3, by decide⟩), (1881, ⟨0, by decide⟩), (1883, ⟨3, by decide⟩),
  (1884, ⟨3, by decide⟩), (1886, ⟨18, by decide⟩), (1888, ⟨32, by decide⟩), (1890, ⟨35, by decide⟩),
  (1892, ⟨0, by decide⟩), (1893, ⟨3, by decide⟩), (1894, ⟨10, by decide⟩), (1895, ⟨3, by decide⟩),
  (1896, ⟨38, by decide⟩), (1897, ⟨38, by decide⟩), (1898, ⟨3, by decide⟩), (1899, ⟨3, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1900, ⟨21, by decide⟩), (1901, ⟨3, by decide⟩), (1902, ⟨23, by decide⟩), (1903, ⟨3, by decide⟩),
  (1904, ⟨23, by decide⟩), (1905, ⟨3, by decide⟩), (1906, ⟨3, by decide⟩), (1907, ⟨3, by decide⟩),
  (1908, ⟨21, by decide⟩), (1909, ⟨10, by decide⟩), (1910, ⟨45, by decide⟩), (1911, ⟨18, by decide⟩),
  (1912, ⟨25, by decide⟩), (1913, ⟨38, by decide⟩), (1914, ⟨38, by decide⟩), (1915, ⟨45, by decide⟩),
  (1916, ⟨0, by decide⟩), (1917, ⟨18, by decide⟩), (1918, ⟨38, by decide⟩), (1919, ⟨23, by decide⟩),
  (1920, ⟨45, by decide⟩), (1921, ⟨19, by decide⟩), (1922, ⟨25, by decide⟩), (1923, ⟨29, by decide⟩),
  (1924, ⟨35, by decide⟩), (1925, ⟨13, by decide⟩), (1926, ⟨0, by decide⟩), (1927, ⟨32, by decide⟩),
  (1928, ⟨19, by decide⟩), (1929, ⟨19, by decide⟩), (1930, ⟨45, by decide⟩), (1931, ⟨25, by decide⟩)
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

theorem keys_match : baselineArrayChunk26.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C26
