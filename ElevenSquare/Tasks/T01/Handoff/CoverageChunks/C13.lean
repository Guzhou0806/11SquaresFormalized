import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C13
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (856, ⟨40, by decide⟩), (857, ⟨21, by decide⟩), (858, ⟨53, by decide⟩), (859, ⟨3, by decide⟩),
  (860, ⟨3, by decide⟩), (861, ⟨53, by decide⟩), (862, ⟨53, by decide⟩), (863, ⟨3, by decide⟩),
  (864, ⟨21, by decide⟩), (865, ⟨21, by decide⟩), (866, ⟨21, by decide⟩), (867, ⟨8, by decide⟩),
  (869, ⟨21, by decide⟩), (870, ⟨40, by decide⟩), (871, ⟨8, by decide⟩), (872, ⟨53, by decide⟩),
  (873, ⟨42, by decide⟩), (874, ⟨8, by decide⟩), (875, ⟨53, by decide⟩), (876, ⟨8, by decide⟩),
  (878, ⟨21, by decide⟩), (879, ⟨21, by decide⟩), (880, ⟨21, by decide⟩), (881, ⟨40, by decide⟩),
  (882, ⟨21, by decide⟩), (883, ⟨53, by decide⟩), (884, ⟨40, by decide⟩), (885, ⟨3, by decide⟩),
  (886, ⟨55, by decide⟩), (887, ⟨7, by decide⟩), (888, ⟨22, by decide⟩), (889, ⟨55, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (890, ⟨3, by decide⟩), (891, ⟨3, by decide⟩), (892, ⟨54, by decide⟩), (893, ⟨55, by decide⟩),
  (895, ⟨0, by decide⟩), (896, ⟨3, by decide⟩), (897, ⟨36, by decide⟩), (898, ⟨0, by decide⟩),
  (899, ⟨0, by decide⟩), (900, ⟨46, by decide⟩), (901, ⟨0, by decide⟩), (902, ⟨0, by decide⟩),
  (903, ⟨3, by decide⟩), (904, ⟨0, by decide⟩), (905, ⟨3, by decide⟩), (906, ⟨3, by decide⟩),
  (907, ⟨22, by decide⟩), (908, ⟨40, by decide⟩), (909, ⟨22, by decide⟩), (910, ⟨22, by decide⟩),
  (911, ⟨3, by decide⟩), (912, ⟨3, by decide⟩), (913, ⟨3, by decide⟩), (914, ⟨22, by decide⟩),
  (915, ⟨3, by decide⟩), (916, ⟨36, by decide⟩), (917, ⟨36, by decide⟩), (918, ⟨22, by decide⟩),
  (920, ⟨39, by decide⟩), (921, ⟨22, by decide⟩), (922, ⟨40, by decide⟩), (923, ⟨22, by decide⟩)
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

theorem keys_match : baselineArrayChunk13.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C13
