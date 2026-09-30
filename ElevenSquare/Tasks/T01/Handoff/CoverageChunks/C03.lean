import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C03
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (192, ⟨36, by decide⟩), (193, ⟨36, by decide⟩), (194, ⟨36, by decide⟩), (195, ⟨5, by decide⟩),
  (196, ⟨37, by decide⟩), (197, ⟨50, by decide⟩), (198, ⟨7, by decide⟩), (199, ⟨6, by decide⟩),
  (200, ⟨50, by decide⟩), (201, ⟨37, by decide⟩), (202, ⟨37, by decide⟩), (203, ⟨54, by decide⟩),
  (204, ⟨50, by decide⟩), (205, ⟨6, by decide⟩), (206, ⟨37, by decide⟩), (207, ⟨37, by decide⟩),
  (208, ⟨37, by decide⟩), (209, ⟨0, by decide⟩), (210, ⟨0, by decide⟩), (211, ⟨46, by decide⟩),
  (212, ⟨37, by decide⟩), (213, ⟨37, by decide⟩), (214, ⟨37, by decide⟩), (215, ⟨22, by decide⟩),
  (216, ⟨3, by decide⟩), (217, ⟨3, by decide⟩), (218, ⟨3, by decide⟩), (219, ⟨17, by decide⟩),
  (220, ⟨86, by decide⟩), (222, ⟨3, by decide⟩), (223, ⟨3, by decide⟩), (224, ⟨3, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (225, ⟨22, by decide⟩), (226, ⟨3, by decide⟩), (227, ⟨3, by decide⟩), (228, ⟨3, by decide⟩),
  (229, ⟨22, by decide⟩), (230, ⟨22, by decide⟩), (231, ⟨6, by decide⟩), (232, ⟨6, by decide⟩),
  (233, ⟨6, by decide⟩), (234, ⟨17, by decide⟩), (235, ⟨6, by decide⟩), (236, ⟨6, by decide⟩),
  (237, ⟨43, by decide⟩), (238, ⟨6, by decide⟩), (239, ⟨6, by decide⟩), (240, ⟨6, by decide⟩),
  (241, ⟨6, by decide⟩), (242, ⟨6, by decide⟩), (243, ⟨6, by decide⟩), (244, ⟨6, by decide⟩),
  (245, ⟨6, by decide⟩), (246, ⟨17, by decide⟩), (249, ⟨17, by decide⟩), (252, ⟨4, by decide⟩),
  (253, ⟨3, by decide⟩), (254, ⟨13, by decide⟩), (255, ⟨4, by decide⟩), (256, ⟨4, by decide⟩),
  (257, ⟨3, by decide⟩), (258, ⟨45, by decide⟩), (259, ⟨4, by decide⟩), (260, ⟨36, by decide⟩)
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

theorem keys_match : baselineArrayChunk3.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C03
