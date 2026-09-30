import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C14
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (924, ⟨22, by decide⟩), (925, ⟨43, by decide⟩), (930, ⟨36, by decide⟩), (931, ⟨36, by decide⟩),
  (932, ⟨36, by decide⟩), (933, ⟨40, by decide⟩), (934, ⟨22, by decide⟩), (935, ⟨22, by decide⟩),
  (936, ⟨40, by decide⟩), (937, ⟨55, by decide⟩), (938, ⟨7, by decide⟩), (939, ⟨28, by decide⟩),
  (940, ⟨7, by decide⟩), (941, ⟨55, by decide⟩), (942, ⟨46, by decide⟩), (943, ⟨51, by decide⟩),
  (944, ⟨55, by decide⟩), (945, ⟨3, by decide⟩), (946, ⟨54, by decide⟩), (947, ⟨0, by decide⟩),
  (948, ⟨0, by decide⟩), (949, ⟨46, by decide⟩), (950, ⟨46, by decide⟩), (951, ⟨40, by decide⟩),
  (952, ⟨3, by decide⟩), (953, ⟨3, by decide⟩), (954, ⟨43, by decide⟩), (957, ⟨3, by decide⟩),
  (959, ⟨23, by decide⟩), (960, ⟨22, by decide⟩), (961, ⟨3, by decide⟩), (962, ⟨3, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (963, ⟨3, by decide⟩), (964, ⟨38, by decide⟩), (967, ⟨45, by decide⟩), (968, ⟨3, by decide⟩),
  (969, ⟨36, by decide⟩), (971, ⟨36, by decide⟩), (972, ⟨36, by decide⟩), (973, ⟨3, by decide⟩),
  (974, ⟨3, by decide⟩), (975, ⟨3, by decide⟩), (976, ⟨36, by decide⟩), (977, ⟨3, by decide⟩),
  (978, ⟨3, by decide⟩), (979, ⟨22, by decide⟩), (980, ⟨46, by decide⟩), (981, ⟨22, by decide⟩),
  (982, ⟨20, by decide⟩), (983, ⟨3, by decide⟩), (984, ⟨3, by decide⟩), (985, ⟨3, by decide⟩),
  (986, ⟨36, by decide⟩), (987, ⟨3, by decide⟩), (988, ⟨36, by decide⟩), (989, ⟨36, by decide⟩),
  (990, ⟨36, by decide⟩), (992, ⟨18, by decide⟩), (993, ⟨22, by decide⟩), (994, ⟨46, by decide⟩),
  (995, ⟨22, by decide⟩), (996, ⟨20, by decide⟩), (1002, ⟨36, by decide⟩), (1003, ⟨36, by decide⟩)
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

theorem keys_match : baselineArrayChunk14.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C14
