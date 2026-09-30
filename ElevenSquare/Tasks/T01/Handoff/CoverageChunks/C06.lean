import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C06
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (389, ⟨3, by decide⟩), (390, ⟨36, by decide⟩), (391, ⟨5, by decide⟩), (392, ⟨36, by decide⟩),
  (393, ⟨36, by decide⟩), (394, ⟨3, by decide⟩), (395, ⟨3, by decide⟩), (396, ⟨3, by decide⟩),
  (397, ⟨36, by decide⟩), (398, ⟨3, by decide⟩), (399, ⟨3, by decide⟩), (400, ⟨22, by decide⟩),
  (401, ⟨5, by decide⟩), (402, ⟨22, by decide⟩), (403, ⟨22, by decide⟩), (404, ⟨3, by decide⟩),
  (405, ⟨3, by decide⟩), (406, ⟨3, by decide⟩), (407, ⟨36, by decide⟩), (408, ⟨3, by decide⟩),
  (409, ⟨36, by decide⟩), (410, ⟨36, by decide⟩), (411, ⟨36, by decide⟩), (412, ⟨36, by decide⟩),
  (413, ⟨5, by decide⟩), (414, ⟨5, by decide⟩), (415, ⟨22, by decide⟩), (416, ⟨21, by decide⟩),
  (417, ⟨22, by decide⟩), (418, ⟨22, by decide⟩), (419, ⟨5, by decide⟩), (420, ⟨5, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (421, ⟨5, by decide⟩), (422, ⟨5, by decide⟩), (423, ⟨5, by decide⟩), (424, ⟨36, by decide⟩),
  (425, ⟨36, by decide⟩), (426, ⟨36, by decide⟩), (427, ⟨5, by decide⟩), (428, ⟨5, by decide⟩),
  (429, ⟨22, by decide⟩), (430, ⟨22, by decide⟩), (431, ⟨22, by decide⟩), (432, ⟨5, by decide⟩),
  (433, ⟨36, by decide⟩), (434, ⟨3, by decide⟩), (435, ⟨19, by decide⟩), (436, ⟨3, by decide⟩),
  (437, ⟨1, by decide⟩), (440, ⟨3, by decide⟩), (441, ⟨3, by decide⟩), (442, ⟨3, by decide⟩),
  (443, ⟨36, by decide⟩), (444, ⟨3, by decide⟩), (445, ⟨3, by decide⟩), (446, ⟨3, by decide⟩),
  (447, ⟨36, by decide⟩), (448, ⟨36, by decide⟩), (449, ⟨3, by decide⟩), (450, ⟨3, by decide⟩),
  (451, ⟨3, by decide⟩), (452, ⟨36, by decide⟩), (453, ⟨36, by decide⟩), (454, ⟨21, by decide⟩)
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

theorem keys_match : baselineArrayChunk6.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C06
