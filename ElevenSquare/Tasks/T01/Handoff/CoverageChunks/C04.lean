import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C04
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (261, ⟨9, by decide⟩), (262, ⟨3, by decide⟩), (263, ⟨3, by decide⟩), (264, ⟨45, by decide⟩),
  (265, ⟨45, by decide⟩), (266, ⟨4, by decide⟩), (267, ⟨3, by decide⟩), (268, ⟨4, by decide⟩),
  (269, ⟨4, by decide⟩), (270, ⟨22, by decide⟩), (271, ⟨3, by decide⟩), (272, ⟨3, by decide⟩),
  (273, ⟨3, by decide⟩), (274, ⟨4, by decide⟩), (275, ⟨4, by decide⟩), (276, ⟨4, by decide⟩),
  (277, ⟨3, by decide⟩), (278, ⟨3, by decide⟩), (279, ⟨36, by decide⟩), (280, ⟨4, by decide⟩),
  (281, ⟨36, by decide⟩), (282, ⟨36, by decide⟩), (283, ⟨3, by decide⟩), (284, ⟨3, by decide⟩),
  (285, ⟨3, by decide⟩), (286, ⟨36, by decide⟩), (287, ⟨4, by decide⟩), (288, ⟨4, by decide⟩),
  (289, ⟨4, by decide⟩), (290, ⟨22, by decide⟩), (291, ⟨4, by decide⟩), (292, ⟨4, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (293, ⟨4, by decide⟩), (294, ⟨4, by decide⟩), (295, ⟨4, by decide⟩), (296, ⟨4, by decide⟩),
  (297, ⟨4, by decide⟩), (298, ⟨4, by decide⟩), (299, ⟨36, by decide⟩), (300, ⟨4, by decide⟩),
  (301, ⟨36, by decide⟩), (302, ⟨36, by decide⟩), (303, ⟨4, by decide⟩), (304, ⟨4, by decide⟩),
  (305, ⟨4, by decide⟩), (306, ⟨4, by decide⟩), (307, ⟨4, by decide⟩), (308, ⟨4, by decide⟩),
  (309, ⟨22, by decide⟩), (310, ⟨46, by decide⟩), (311, ⟨22, by decide⟩), (312, ⟨22, by decide⟩),
  (313, ⟨4, by decide⟩), (314, ⟨4, by decide⟩), (315, ⟨4, by decide⟩), (316, ⟨4, by decide⟩),
  (317, ⟨4, by decide⟩), (318, ⟨36, by decide⟩), (319, ⟨36, by decide⟩), (320, ⟨36, by decide⟩),
  (321, ⟨4, by decide⟩), (322, ⟨3, by decide⟩), (323, ⟨4, by decide⟩), (324, ⟨4, by decide⟩)
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

theorem keys_match : baselineArrayChunk4.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C04
