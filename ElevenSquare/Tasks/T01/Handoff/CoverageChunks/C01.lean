import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C01
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (64, ⟨18, by decide⟩), (65, ⟨37, by decide⟩), (66, ⟨37, by decide⟩), (67, ⟨37, by decide⟩),
  (68, ⟨0, by decide⟩), (69, ⟨0, by decide⟩), (70, ⟨6, by decide⟩), (71, ⟨3, by decide⟩),
  (72, ⟨4, by decide⟩), (73, ⟨4, by decide⟩), (74, ⟨21, by decide⟩), (75, ⟨3, by decide⟩),
  (76, ⟨3, by decide⟩), (77, ⟨3, by decide⟩), (78, ⟨4, by decide⟩), (79, ⟨4, by decide⟩),
  (80, ⟨53, by decide⟩), (81, ⟨3, by decide⟩), (82, ⟨3, by decide⟩), (83, ⟨21, by decide⟩),
  (84, ⟨4, by decide⟩), (85, ⟨21, by decide⟩), (86, ⟨21, by decide⟩), (87, ⟨3, by decide⟩),
  (88, ⟨3, by decide⟩), (89, ⟨3, by decide⟩), (90, ⟨22, by decide⟩), (91, ⟨6, by decide⟩),
  (92, ⟨8, by decide⟩), (93, ⟨6, by decide⟩), (94, ⟨21, by decide⟩), (95, ⟨8, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (96, ⟨6, by decide⟩), (97, ⟨6, by decide⟩), (98, ⟨8, by decide⟩), (99, ⟨8, by decide⟩),
  (100, ⟨53, by decide⟩), (101, ⟨6, by decide⟩), (102, ⟨6, by decide⟩), (103, ⟨21, by decide⟩),
  (104, ⟨6, by decide⟩), (105, ⟨21, by decide⟩), (106, ⟨21, by decide⟩), (107, ⟨6, by decide⟩),
  (108, ⟨6, by decide⟩), (109, ⟨6, by decide⟩), (110, ⟨6, by decide⟩), (111, ⟨4, by decide⟩),
  (112, ⟨4, by decide⟩), (113, ⟨21, by decide⟩), (114, ⟨17, by decide⟩), (115, ⟨21, by decide⟩),
  (116, ⟨43, by decide⟩), (117, ⟨4, by decide⟩), (118, ⟨4, by decide⟩), (119, ⟨53, by decide⟩),
  (120, ⟨53, by decide⟩), (121, ⟨4, by decide⟩), (122, ⟨21, by decide⟩), (123, ⟨21, by decide⟩),
  (124, ⟨21, by decide⟩), (125, ⟨4, by decide⟩), (126, ⟨6, by decide⟩), (127, ⟨37, by decide⟩)
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

theorem keys_match : baselineArrayChunk1.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C01
