import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C12
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (791, ⟨23, by decide⟩), (792, ⟨1, by decide⟩), (793, ⟨23, by decide⟩), (794, ⟨23, by decide⟩),
  (795, ⟨3, by decide⟩), (796, ⟨3, by decide⟩), (797, ⟨3, by decide⟩), (798, ⟨22, by decide⟩),
  (799, ⟨2, by decide⟩), (800, ⟨8, by decide⟩), (801, ⟨2, by decide⟩), (802, ⟨10, by decide⟩),
  (803, ⟨8, by decide⟩), (804, ⟨2, by decide⟩), (805, ⟨2, by decide⟩), (806, ⟨35, by decide⟩),
  (807, ⟨8, by decide⟩), (808, ⟨26, by decide⟩), (809, ⟨24, by decide⟩), (810, ⟨1, by decide⟩),
  (811, ⟨21, by decide⟩), (812, ⟨24, by decide⟩), (813, ⟨24, by decide⟩), (814, ⟨21, by decide⟩),
  (815, ⟨31, by decide⟩), (816, ⟨31, by decide⟩), (818, ⟨31, by decide⟩), (819, ⟨2, by decide⟩),
  (820, ⟨2, by decide⟩), (821, ⟨10, by decide⟩), (822, ⟨7, by decide⟩), (823, ⟨10, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (824, ⟨10, by decide⟩), (825, ⟨2, by decide⟩), (826, ⟨58, by decide⟩), (827, ⟨53, by decide⟩),
  (828, ⟨53, by decide⟩), (829, ⟨1, by decide⟩), (830, ⟨21, by decide⟩), (831, ⟨21, by decide⟩),
  (832, ⟨21, by decide⟩), (833, ⟨3, by decide⟩), (834, ⟨8, by decide⟩), (835, ⟨7, by decide⟩),
  (836, ⟨26, by decide⟩), (837, ⟨8, by decide⟩), (838, ⟨3, by decide⟩), (839, ⟨32, by decide⟩),
  (840, ⟨38, by decide⟩), (841, ⟨32, by decide⟩), (842, ⟨32, by decide⟩), (843, ⟨0, by decide⟩),
  (844, ⟨3, by decide⟩), (845, ⟨21, by decide⟩), (846, ⟨0, by decide⟩), (847, ⟨0, by decide⟩),
  (848, ⟨46, by decide⟩), (849, ⟨0, by decide⟩), (850, ⟨0, by decide⟩), (851, ⟨3, by decide⟩),
  (852, ⟨0, by decide⟩), (853, ⟨3, by decide⟩), (854, ⟨3, by decide⟩), (855, ⟨21, by decide⟩)
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

theorem keys_match : baselineArrayChunk12.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C12
