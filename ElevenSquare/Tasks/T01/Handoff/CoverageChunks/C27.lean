import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C27
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1932, ⟨25, by decide⟩), (1933, ⟨15, by decide⟩), (1934, ⟨25, by decide⟩), (1935, ⟨27, by decide⟩),
  (1936, ⟨25, by decide⟩), (1937, ⟨25, by decide⟩), (1938, ⟨47, by decide⟩), (1939, ⟨27, by decide⟩),
  (1940, ⟨25, by decide⟩), (1941, ⟨25, by decide⟩), (1942, ⟨25, by decide⟩), (1943, ⟨27, by decide⟩),
  (1944, ⟨3, by decide⟩), (1945, ⟨44, by decide⟩), (1946, ⟨3, by decide⟩), (1947, ⟨47, by decide⟩),
  (1948, ⟨47, by decide⟩), (1949, ⟨3, by decide⟩), (1951, ⟨48, by decide⟩), (1952, ⟨3, by decide⟩),
  (1953, ⟨32, by decide⟩), (1954, ⟨47, by decide⟩), (1956, ⟨15, by decide⟩), (1957, ⟨3, by decide⟩),
  (1958, ⟨10, by decide⟩), (1959, ⟨10, by decide⟩), (1960, ⟨3, by decide⟩), (1961, ⟨3, by decide⟩),
  (1962, ⟨3, by decide⟩), (1963, ⟨21, by decide⟩), (1964, ⟨3, by decide⟩), (1965, ⟨23, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (1966, ⟨23, by decide⟩), (1967, ⟨3, by decide⟩), (1968, ⟨3, by decide⟩), (1969, ⟨3, by decide⟩),
  (1970, ⟨21, by decide⟩), (1971, ⟨10, by decide⟩), (1972, ⟨3, by decide⟩), (1973, ⟨18, by decide⟩),
  (1974, ⟨23, by decide⟩), (1975, ⟨3, by decide⟩), (1976, ⟨3, by decide⟩), (1977, ⟨37, by decide⟩),
  (1978, ⟨18, by decide⟩), (1979, ⟨1, by decide⟩), (1980, ⟨23, by decide⟩), (1981, ⟨27, by decide⟩),
  (1982, ⟨44, by decide⟩), (1983, ⟨29, by decide⟩), (1984, ⟨27, by decide⟩), (1985, ⟨27, by decide⟩),
  (1986, ⟨34, by decide⟩), (1987, ⟨48, by decide⟩), (1988, ⟨19, by decide⟩), (1989, ⟨19, by decide⟩),
  (1990, ⟨37, by decide⟩), (1991, ⟨3, by decide⟩), (1992, ⟨18, by decide⟩), (1993, ⟨29, by decide⟩),
  (1994, ⟨35, by decide⟩), (1995, ⟨3, by decide⟩), (1996, ⟨3, by decide⟩), (1997, ⟨18, by decide⟩)
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

theorem keys_match : baselineArrayChunk27.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C27
