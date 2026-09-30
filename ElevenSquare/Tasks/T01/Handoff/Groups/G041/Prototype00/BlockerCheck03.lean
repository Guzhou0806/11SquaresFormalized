import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.BlockerData

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target03_checked :
    (SymbolicFieldTarget.blocker target03 point08b (49999/100000)).Check := by
  change 0 ≤ (49999/100000:ℚ) ∧ (49999/100000:ℚ) < 1/2 ∧
    ∀ f ∈ symbolicPointTarget point08b (49999/100000), f ∈ target03
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f hf
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp
    (show f ∈ (List.finRange 4).map (symbolicPointFacet point08b (49999/100000))
      by simpa only [symbolicPointTarget] using hf)
  fin_cases k <;>
    norm_num [symbolicPointFacet, symbolicPointNormal,
      symbolicPointBound, point08b, target03]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.target03_checked
