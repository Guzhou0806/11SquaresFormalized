import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C30
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (2167, ⟨19, by decide⟩), (2168, ⟨19, by decide⟩), (2169, ⟨19, by decide⟩), (2170, ⟨19, by decide⟩),
  (2171, ⟨19, by decide⟩), (2172, ⟨19, by decide⟩), (2173, ⟨92, by decide⟩), (2177, ⟨12, by decide⟩),
  (2179, ⟨45, by decide⟩), (2180, ⟨9, by decide⟩), (2181, ⟨9, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def assignments : List (ℕ × Group) := part0
theorem valid : List.Forall (fun p => p.1 ∈ groupCases p.2) assignments := by
  exact part0_valid

theorem keys_match : baselineArrayChunk30.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C30
