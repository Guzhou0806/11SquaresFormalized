import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C02
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (128, ⟨50, by decide⟩), (129, ⟨6, by decide⟩), (130, ⟨6, by decide⟩), (131, ⟨37, by decide⟩),
  (132, ⟨0, by decide⟩), (133, ⟨6, by decide⟩), (134, ⟨36, by decide⟩), (135, ⟨37, by decide⟩),
  (136, ⟨37, by decide⟩), (137, ⟨37, by decide⟩), (138, ⟨0, by decide⟩), (139, ⟨0, by decide⟩),
  (140, ⟨6, by decide⟩), (141, ⟨3, by decide⟩), (142, ⟨5, by decide⟩), (143, ⟨5, by decide⟩),
  (144, ⟨22, by decide⟩), (145, ⟨3, by decide⟩), (146, ⟨3, by decide⟩), (147, ⟨3, by decide⟩),
  (148, ⟨5, by decide⟩), (149, ⟨5, by decide⟩), (150, ⟨5, by decide⟩), (151, ⟨3, by decide⟩),
  (152, ⟨3, by decide⟩), (153, ⟨36, by decide⟩), (154, ⟨5, by decide⟩), (155, ⟨36, by decide⟩),
  (156, ⟨36, by decide⟩), (157, ⟨3, by decide⟩), (158, ⟨3, by decide⟩), (159, ⟨3, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (160, ⟨22, by decide⟩), (161, ⟨6, by decide⟩), (162, ⟨6, by decide⟩), (163, ⟨6, by decide⟩),
  (164, ⟨22, by decide⟩), (165, ⟨6, by decide⟩), (166, ⟨6, by decide⟩), (167, ⟨6, by decide⟩),
  (168, ⟨6, by decide⟩), (169, ⟨6, by decide⟩), (170, ⟨6, by decide⟩), (171, ⟨6, by decide⟩),
  (172, ⟨6, by decide⟩), (173, ⟨36, by decide⟩), (174, ⟨6, by decide⟩), (175, ⟨36, by decide⟩),
  (176, ⟨36, by decide⟩), (177, ⟨6, by decide⟩), (178, ⟨6, by decide⟩), (179, ⟨6, by decide⟩),
  (180, ⟨6, by decide⟩), (181, ⟨5, by decide⟩), (182, ⟨5, by decide⟩), (183, ⟨22, by decide⟩),
  (184, ⟨17, by decide⟩), (185, ⟨22, by decide⟩), (186, ⟨22, by decide⟩), (187, ⟨5, by decide⟩),
  (188, ⟨5, by decide⟩), (189, ⟨5, by decide⟩), (190, ⟨5, by decide⟩), (191, ⟨5, by decide⟩)
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

theorem keys_match : baselineArrayChunk2.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C02
