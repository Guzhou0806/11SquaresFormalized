import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C28
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (1998, ⟨10, by decide⟩), (1999, ⟨23, by decide⟩), (2000, ⟨18, by decide⟩), (2001, ⟨29, by decide⟩),
  (2002, ⟨1, by decide⟩), (2003, ⟨37, by decide⟩), (2004, ⟨13, by decide⟩), (2005, ⟨19, by decide⟩),
  (2006, ⟨37, by decide⟩), (2007, ⟨45, by decide⟩), (2008, ⟨1, by decide⟩), (2009, ⟨9, by decide⟩),
  (2010, ⟨37, by decide⟩), (2011, ⟨45, by decide⟩), (2012, ⟨1, by decide⟩), (2013, ⟨1, by decide⟩),
  (2014, ⟨1, by decide⟩), (2015, ⟨19, by decide⟩), (2016, ⟨19, by decide⟩), (2017, ⟨19, by decide⟩),
  (2018, ⟨1, by decide⟩), (2019, ⟨1, by decide⟩), (2020, ⟨1, by decide⟩), (2021, ⟨19, by decide⟩),
  (2022, ⟨1, by decide⟩), (2023, ⟨38, by decide⟩), (2024, ⟨1, by decide⟩), (2025, ⟨19, by decide⟩),
  (2026, ⟨19, by decide⟩), (2027, ⟨19, by decide⟩), (2028, ⟨38, by decide⟩), (2029, ⟨1, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (2030, ⟨38, by decide⟩), (2031, ⟨19, by decide⟩), (2032, ⟨1, by decide⟩), (2033, ⟨1, by decide⟩),
  (2034, ⟨7, by decide⟩), (2035, ⟨19, by decide⟩), (2036, ⟨1, by decide⟩), (2037, ⟨37, by decide⟩),
  (2038, ⟨0, by decide⟩), (2039, ⟨7, by decide⟩), (2040, ⟨37, by decide⟩), (2041, ⟨37, by decide⟩),
  (2042, ⟨38, by decide⟩), (2043, ⟨37, by decide⟩), (2044, ⟨37, by decide⟩), (2045, ⟨0, by decide⟩),
  (2046, ⟨37, by decide⟩), (2054, ⟨83, by decide⟩), (2058, ⟨37, by decide⟩), (2059, ⟨0, by decide⟩),
  (2060, ⟨7, by decide⟩), (2061, ⟨37, by decide⟩), (2062, ⟨37, by decide⟩), (2063, ⟨0, by decide⟩),
  (2064, ⟨37, by decide⟩), (2065, ⟨37, by decide⟩), (2066, ⟨0, by decide⟩), (2067, ⟨37, by decide⟩),
  (2079, ⟨37, by decide⟩), (2080, ⟨7, by decide⟩), (2081, ⟨7, by decide⟩), (2082, ⟨37, by decide⟩)
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

theorem keys_match : baselineArrayChunk28.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C28
