import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C09
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (585, ⟨55, by decide⟩), (586, ⟨58, by decide⟩), (587, ⟨22, by decide⟩), (588, ⟨55, by decide⟩),
  (589, ⟨5, by decide⟩), (590, ⟨5, by decide⟩), (591, ⟨54, by decide⟩), (592, ⟨55, by decide⟩),
  (593, ⟨5, by decide⟩), (594, ⟨5, by decide⟩), (595, ⟨5, by decide⟩), (596, ⟨36, by decide⟩),
  (597, ⟨5, by decide⟩), (598, ⟨36, by decide⟩), (599, ⟨36, by decide⟩), (600, ⟨5, by decide⟩),
  (601, ⟨5, by decide⟩), (602, ⟨5, by decide⟩), (603, ⟨5, by decide⟩), (604, ⟨5, by decide⟩),
  (605, ⟨5, by decide⟩), (606, ⟨22, by decide⟩), (607, ⟨5, by decide⟩), (608, ⟨22, by decide⟩),
  (609, ⟨22, by decide⟩), (610, ⟨5, by decide⟩), (611, ⟨5, by decide⟩), (612, ⟨5, by decide⟩),
  (613, ⟨5, by decide⟩), (614, ⟨5, by decide⟩), (615, ⟨36, by decide⟩), (616, ⟨36, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (617, ⟨36, by decide⟩), (618, ⟨5, by decide⟩), (619, ⟨5, by decide⟩), (620, ⟨5, by decide⟩),
  (621, ⟨22, by decide⟩), (622, ⟨53, by decide⟩), (623, ⟨22, by decide⟩), (624, ⟨22, by decide⟩),
  (625, ⟨5, by decide⟩), (626, ⟨5, by decide⟩), (627, ⟨5, by decide⟩), (628, ⟨5, by decide⟩),
  (629, ⟨5, by decide⟩), (630, ⟨36, by decide⟩), (631, ⟨36, by decide⟩), (632, ⟨36, by decide⟩),
  (633, ⟨5, by decide⟩), (634, ⟨5, by decide⟩), (635, ⟨22, by decide⟩), (636, ⟨22, by decide⟩),
  (637, ⟨22, by decide⟩), (638, ⟨5, by decide⟩), (639, ⟨55, by decide⟩), (640, ⟨58, by decide⟩),
  (641, ⟨28, by decide⟩), (642, ⟨58, by decide⟩), (643, ⟨55, by decide⟩), (644, ⟨87, by decide⟩),
  (645, ⟨51, by decide⟩), (646, ⟨55, by decide⟩), (648, ⟨54, by decide⟩), (653, ⟨4, by decide⟩)
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

theorem keys_match : baselineArrayChunk9.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C09
