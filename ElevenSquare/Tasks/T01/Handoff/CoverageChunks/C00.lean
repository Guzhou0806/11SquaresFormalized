import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C00
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (0, ⟨2, by decide⟩), (1, ⟨1, by decide⟩), (2, ⟨37, by decide⟩), (3, ⟨11, by decide⟩),
  (4, ⟨25, by decide⟩), (5, ⟨25, by decide⟩), (6, ⟨2, by decide⟩), (7, ⟨3, by decide⟩),
  (8, ⟨2, by decide⟩), (9, ⟨2, by decide⟩), (10, ⟨2, by decide⟩), (11, ⟨1, by decide⟩),
  (12, ⟨1, by decide⟩), (13, ⟨1, by decide⟩), (14, ⟨23, by decide⟩), (15, ⟨3, by decide⟩),
  (16, ⟨3, by decide⟩), (17, ⟨3, by decide⟩), (18, ⟨19, by decide⟩), (19, ⟨19, by decide⟩),
  (20, ⟨19, by decide⟩), (21, ⟨2, by decide⟩), (22, ⟨2, by decide⟩), (23, ⟨8, by decide⟩),
  (24, ⟨2, by decide⟩), (25, ⟨2, by decide⟩), (26, ⟨1, by decide⟩), (27, ⟨24, by decide⟩),
  (28, ⟨1, by decide⟩), (29, ⟨21, by decide⟩), (30, ⟨31, by decide⟩), (31, ⟨6, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (32, ⟨6, by decide⟩), (33, ⟨31, by decide⟩), (34, ⟨31, by decide⟩), (35, ⟨6, by decide⟩),
  (36, ⟨2, by decide⟩), (37, ⟨2, by decide⟩), (38, ⟨15, by decide⟩), (39, ⟨10, by decide⟩),
  (40, ⟨2, by decide⟩), (41, ⟨2, by decide⟩), (42, ⟨2, by decide⟩), (43, ⟨47, by decide⟩),
  (44, ⟨2, by decide⟩), (45, ⟨49, by decide⟩), (46, ⟨1, by decide⟩), (47, ⟨1, by decide⟩),
  (48, ⟨21, by decide⟩), (49, ⟨1, by decide⟩), (50, ⟨21, by decide⟩), (51, ⟨21, by decide⟩),
  (52, ⟨19, by decide⟩), (53, ⟨19, by decide⟩), (54, ⟨19, by decide⟩), (55, ⟨19, by decide⟩),
  (56, ⟨6, by decide⟩), (57, ⟨37, by decide⟩), (58, ⟨16, by decide⟩), (59, ⟨6, by decide⟩),
  (60, ⟨32, by decide⟩), (61, ⟨37, by decide⟩), (62, ⟨0, by decide⟩), (63, ⟨6, by decide⟩)
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

theorem keys_match : baselineArrayChunk0.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C00
