import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C07
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (457, ⟨21, by decide⟩), (458, ⟨4, by decide⟩), (459, ⟨4, by decide⟩), (460, ⟨4, by decide⟩),
  (461, ⟨11, by decide⟩), (462, ⟨4, by decide⟩), (463, ⟨52, by decide⟩), (464, ⟨4, by decide⟩),
  (465, ⟨24, by decide⟩), (466, ⟨4, by decide⟩), (467, ⟨36, by decide⟩), (468, ⟨27, by decide⟩),
  (469, ⟨4, by decide⟩), (470, ⟨4, by decide⟩), (471, ⟨11, by decide⟩), (472, ⟨11, by decide⟩),
  (473, ⟨4, by decide⟩), (474, ⟨4, by decide⟩), (475, ⟨4, by decide⟩), (476, ⟨4, by decide⟩),
  (477, ⟨22, by decide⟩), (478, ⟨4, by decide⟩), (479, ⟨4, by decide⟩), (480, ⟨4, by decide⟩),
  (481, ⟨4, by decide⟩), (482, ⟨4, by decide⟩), (483, ⟨51, by decide⟩), (484, ⟨4, by decide⟩),
  (485, ⟨4, by decide⟩), (486, ⟨36, by decide⟩), (487, ⟨4, by decide⟩), (488, ⟨36, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (489, ⟨36, by decide⟩), (490, ⟨4, by decide⟩), (491, ⟨4, by decide⟩), (492, ⟨4, by decide⟩),
  (493, ⟨4, by decide⟩), (494, ⟨4, by decide⟩), (495, ⟨24, by decide⟩), (496, ⟨4, by decide⟩),
  (497, ⟨22, by decide⟩), (498, ⟨31, by decide⟩), (499, ⟨4, by decide⟩), (500, ⟨4, by decide⟩),
  (501, ⟨35, by decide⟩), (502, ⟨31, by decide⟩), (503, ⟨51, by decide⟩), (504, ⟨24, by decide⟩),
  (505, ⟨4, by decide⟩), (506, ⟨36, by decide⟩), (507, ⟨24, by decide⟩), (508, ⟨24, by decide⟩),
  (509, ⟨36, by decide⟩), (510, ⟨31, by decide⟩), (511, ⟨31, by decide⟩), (512, ⟨4, by decide⟩),
  (513, ⟨31, by decide⟩), (514, ⟨4, by decide⟩), (515, ⟨4, by decide⟩), (516, ⟨22, by decide⟩),
  (517, ⟨0, by decide⟩), (518, ⟨22, by decide⟩), (519, ⟨43, by decide⟩), (520, ⟨4, by decide⟩)
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

theorem keys_match : baselineArrayChunk7.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C07
