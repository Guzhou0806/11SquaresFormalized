import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C29
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (2083, ⟨37, by decide⟩), (2085, ⟨13, by decide⟩), (2086, ⟨72, by decide⟩), (2087, ⟨13, by decide⟩),
  (2089, ⟨13, by decide⟩), (2090, ⟨9, by decide⟩), (2092, ⟨45, by decide⟩), (2093, ⟨9, by decide⟩),
  (2095, ⟨88, by decide⟩), (2096, ⟨0, by decide⟩), (2099, ⟨89, by decide⟩), (2100, ⟨77, by decide⟩),
  (2101, ⟨0, by decide⟩), (2104, ⟨68, by decide⟩), (2105, ⟨19, by decide⟩), (2106, ⟨38, by decide⟩),
  (2107, ⟨38, by decide⟩), (2108, ⟨91, by decide⟩), (2109, ⟨19, by decide⟩), (2110, ⟨1, by decide⟩),
  (2113, ⟨38, by decide⟩), (2115, ⟨9, by decide⟩), (2117, ⟨71, by decide⟩), (2118, ⟨9, by decide⟩),
  (2120, ⟨38, by decide⟩), (2121, ⟨9, by decide⟩), (2123, ⟨90, by decide⟩), (2124, ⟨0, by decide⟩),
  (2126, ⟨38, by decide⟩), (2127, ⟨70, by decide⟩), (2128, ⟨38, by decide⟩), (2131, ⟨19, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (2134, ⟨19, by decide⟩), (2136, ⟨9, by decide⟩), (2137, ⟨19, by decide⟩), (2138, ⟨0, by decide⟩),
  (2139, ⟨1, by decide⟩), (2140, ⟨12, by decide⟩), (2141, ⟨12, by decide⟩), (2142, ⟨0, by decide⟩),
  (2143, ⟨67, by decide⟩), (2144, ⟨38, by decide⟩), (2145, ⟨45, by decide⟩), (2146, ⟨1, by decide⟩),
  (2147, ⟨38, by decide⟩), (2148, ⟨1, by decide⟩), (2149, ⟨1, by decide⟩), (2150, ⟨7, by decide⟩),
  (2151, ⟨38, by decide⟩), (2152, ⟨1, by decide⟩), (2153, ⟨7, by decide⟩), (2154, ⟨0, by decide⟩),
  (2155, ⟨7, by decide⟩), (2156, ⟨0, by decide⟩), (2157, ⟨7, by decide⟩), (2158, ⟨61, by decide⟩),
  (2159, ⟨19, by decide⟩), (2160, ⟨45, by decide⟩), (2161, ⟨19, by decide⟩), (2162, ⟨19, by decide⟩),
  (2163, ⟨12, by decide⟩), (2164, ⟨19, by decide⟩), (2165, ⟨19, by decide⟩), (2166, ⟨19, by decide⟩)
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

theorem keys_match : baselineArrayChunk29.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C29
