import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C05
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (325, ⟨4, by decide⟩), (326, ⟨3, by decide⟩), (327, ⟨3, by decide⟩), (328, ⟨3, by decide⟩),
  (329, ⟨38, by decide⟩), (330, ⟨4, by decide⟩), (331, ⟨4, by decide⟩), (332, ⟨3, by decide⟩),
  (333, ⟨3, by decide⟩), (334, ⟨3, by decide⟩), (335, ⟨4, by decide⟩), (336, ⟨4, by decide⟩),
  (337, ⟨4, by decide⟩), (338, ⟨3, by decide⟩), (339, ⟨3, by decide⟩), (340, ⟨3, by decide⟩),
  (341, ⟨36, by decide⟩), (342, ⟨3, by decide⟩), (343, ⟨3, by decide⟩), (344, ⟨3, by decide⟩),
  (345, ⟨4, by decide⟩), (346, ⟨4, by decide⟩), (347, ⟨4, by decide⟩), (348, ⟨3, by decide⟩),
  (349, ⟨3, by decide⟩), (350, ⟨3, by decide⟩), (351, ⟨36, by decide⟩), (352, ⟨3, by decide⟩),
  (353, ⟨3, by decide⟩), (354, ⟨3, by decide⟩), (355, ⟨36, by decide⟩), (356, ⟨36, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (357, ⟨4, by decide⟩), (358, ⟨4, by decide⟩), (359, ⟨4, by decide⟩), (360, ⟨21, by decide⟩),
  (361, ⟨4, by decide⟩), (362, ⟨4, by decide⟩), (363, ⟨4, by decide⟩), (364, ⟨4, by decide⟩),
  (365, ⟨4, by decide⟩), (366, ⟨4, by decide⟩), (367, ⟨4, by decide⟩), (368, ⟨4, by decide⟩),
  (369, ⟨4, by decide⟩), (370, ⟨4, by decide⟩), (371, ⟨4, by decide⟩), (372, ⟨4, by decide⟩),
  (373, ⟨4, by decide⟩), (374, ⟨4, by decide⟩), (375, ⟨4, by decide⟩), (376, ⟨4, by decide⟩),
  (377, ⟨4, by decide⟩), (378, ⟨3, by decide⟩), (379, ⟨5, by decide⟩), (380, ⟨23, by decide⟩),
  (381, ⟨22, by decide⟩), (382, ⟨3, by decide⟩), (383, ⟨3, by decide⟩), (384, ⟨3, by decide⟩),
  (385, ⟨5, by decide⟩), (386, ⟨5, by decide⟩), (387, ⟨5, by decide⟩), (388, ⟨3, by decide⟩)
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

theorem keys_match : baselineArrayChunk5.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C05
