import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C10
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (658, ⟨53, by decide⟩), (661, ⟨53, by decide⟩), (662, ⟨4, by decide⟩), (663, ⟨4, by decide⟩),
  (664, ⟨4, by decide⟩), (665, ⟨22, by decide⟩), (666, ⟨9, by decide⟩), (667, ⟨4, by decide⟩),
  (668, ⟨27, by decide⟩), (669, ⟨4, by decide⟩), (670, ⟨4, by decide⟩), (671, ⟨4, by decide⟩),
  (672, ⟨9, by decide⟩), (673, ⟨4, by decide⟩), (674, ⟨36, by decide⟩), (675, ⟨4, by decide⟩),
  (676, ⟨36, by decide⟩), (677, ⟨36, by decide⟩), (678, ⟨9, by decide⟩), (679, ⟨9, by decide⟩),
  (680, ⟨4, by decide⟩), (681, ⟨4, by decide⟩), (682, ⟨4, by decide⟩), (683, ⟨4, by decide⟩),
  (684, ⟨22, by decide⟩), (685, ⟨0, by decide⟩), (686, ⟨22, by decide⟩), (687, ⟨20, by decide⟩),
  (688, ⟨4, by decide⟩), (689, ⟨4, by decide⟩), (690, ⟨4, by decide⟩), (691, ⟨4, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (692, ⟨4, by decide⟩), (693, ⟨36, by decide⟩), (694, ⟨36, by decide⟩), (695, ⟨36, by decide⟩),
  (696, ⟨4, by decide⟩), (697, ⟨4, by decide⟩), (698, ⟨4, by decide⟩), (699, ⟨22, by decide⟩),
  (700, ⟨0, by decide⟩), (701, ⟨22, by decide⟩), (702, ⟨20, by decide⟩), (703, ⟨4, by decide⟩),
  (704, ⟨4, by decide⟩), (705, ⟨4, by decide⟩), (706, ⟨4, by decide⟩), (707, ⟨4, by decide⟩),
  (708, ⟨36, by decide⟩), (709, ⟨36, by decide⟩), (710, ⟨36, by decide⟩), (711, ⟨4, by decide⟩),
  (712, ⟨37, by decide⟩), (713, ⟨22, by decide⟩), (714, ⟨20, by decide⟩), (715, ⟨0, by decide⟩),
  (716, ⟨4, by decide⟩), (717, ⟨19, by decide⟩), (718, ⟨4, by decide⟩), (719, ⟨4, by decide⟩),
  (720, ⟨4, by decide⟩), (721, ⟨4, by decide⟩), (722, ⟨4, by decide⟩), (723, ⟨4, by decide⟩)
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

theorem keys_match : baselineArrayChunk10.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C10
