import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C11
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (724, ⟨4, by decide⟩), (725, ⟨31, by decide⟩), (726, ⟨4, by decide⟩), (727, ⟨4, by decide⟩),
  (728, ⟨4, by decide⟩), (729, ⟨4, by decide⟩), (730, ⟨4, by decide⟩), (731, ⟨4, by decide⟩),
  (732, ⟨4, by decide⟩), (733, ⟨4, by decide⟩), (734, ⟨4, by decide⟩), (735, ⟨4, by decide⟩),
  (736, ⟨4, by decide⟩), (737, ⟨4, by decide⟩), (738, ⟨5, by decide⟩), (739, ⟨19, by decide⟩),
  (740, ⟨22, by decide⟩), (741, ⟨5, by decide⟩), (742, ⟨22, by decide⟩), (743, ⟨22, by decide⟩),
  (744, ⟨5, by decide⟩), (745, ⟨5, by decide⟩), (746, ⟨5, by decide⟩), (747, ⟨5, by decide⟩),
  (748, ⟨5, by decide⟩), (749, ⟨36, by decide⟩), (750, ⟨36, by decide⟩), (751, ⟨36, by decide⟩),
  (752, ⟨5, by decide⟩), (753, ⟨22, by decide⟩), (754, ⟨22, by decide⟩), (755, ⟨22, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (756, ⟨5, by decide⟩), (757, ⟨22, by decide⟩), (758, ⟨22, by decide⟩), (759, ⟨22, by decide⟩),
  (760, ⟨19, by decide⟩), (762, ⟨19, by decide⟩), (764, ⟨2, by decide⟩), (765, ⟨2, by decide⟩),
  (766, ⟨8, by decide⟩), (767, ⟨2, by decide⟩), (768, ⟨29, by decide⟩), (769, ⟨1, by decide⟩),
  (770, ⟨24, by decide⟩), (771, ⟨1, by decide⟩), (772, ⟨23, by decide⟩), (773, ⟨31, by decide⟩),
  (774, ⟨3, by decide⟩), (775, ⟨3, by decide⟩), (776, ⟨31, by decide⟩), (777, ⟨31, by decide⟩),
  (779, ⟨2, by decide⟩), (780, ⟨2, by decide⟩), (781, ⟨2, by decide⟩), (782, ⟨10, by decide⟩),
  (783, ⟨2, by decide⟩), (784, ⟨2, by decide⟩), (785, ⟨2, by decide⟩), (786, ⟨2, by decide⟩),
  (787, ⟨2, by decide⟩), (788, ⟨53, by decide⟩), (789, ⟨1, by decide⟩), (790, ⟨1, by decide⟩)
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

theorem keys_match : baselineArrayChunk11.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C11
