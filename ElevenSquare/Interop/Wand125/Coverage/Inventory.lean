import ElevenSquare.Interop.Wand125.Coverage.Data

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem newCases_baseline : ∀ k ∈ newCases, k ∈ baselineIndices := by
  have h : newCases.Sublist baselineArray.toList := by
    simp only [baselineArray, Array.toList_append]
    decide +kernel
  intro k hk
  exact List.mem_toFinset.mpr (h.subset hk)

#print axioms ElevenSquare.Interop.Wand125.newCases_baseline

theorem newCases_disjoint : ∀ k ∈ newCases,
    k ∉ groupCases (3 : Group) ∧ k ∉ groupCases (4 : Group) ∧
    k ∉ groupCases (7 : Group) := by decide +kernel


end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.newCases_disjoint
