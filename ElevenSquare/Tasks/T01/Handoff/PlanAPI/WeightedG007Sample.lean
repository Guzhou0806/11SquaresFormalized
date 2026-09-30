import ElevenSquare.Tasks.T01.Handoff.PlanAPI.WeightedFeature
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row000.CheckedRow

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Packet G007 has one unit singleton and one unit majority feature. -/
def g007Features (f : Fin 2) : WeightedFeature :=
  if f = 0 then ⟨.point Groups.G007.point, 1⟩
  else ⟨.majority Groups.G007.sites 2, 1⟩

theorem g007Features_valid : ∀ f, (g007Features f).Valid := by
  intro f
  fin_cases f
  · simp [g007Features, WeightedFeature.Valid, WeightedTarget.Valid]
  · simp [g007Features, WeightedFeature.Valid, WeightedTarget.Valid,
      Groups.G007.sites_card]

theorem g007Features_budget : weightedBudget g007Features = 2 := by
  norm_num [weightedBudget, g007Features, Fin.sum_univ_two]

/-- The already checked archived G007 row supplies a concrete unit of
weighted charge. Its independently owned blockers are explicit premises. -/
theorem g007_row000_weighted_charge {S : ℝ} (P : Packing 11 S) (i : Owner)
    (hq : Groups.G007.Cell05Row000.inputRow.contains (P.squares i))
    (howned : ∀ p ∈ Groups.G007.Cell05Row000.forbiddenPoints,
      ∃ j : Owner, i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    1 ≤ weightedCharge g007Features (P.squares i) := by
  classical
  have hc := Groups.G007.Cell05Row000.packing_row_choice P i hq howned
  rcases hc with hp | hm
  · simp [weightedCharge, featureCharge, WeightedFeature.Capture,
      WeightedTarget.Capture, g007Features, hp, Fin.sum_univ_two]
  · simp [weightedCharge, featureCharge, WeightedFeature.Capture,
      WeightedTarget.Capture, g007Features, hm, Fin.sum_univ_two]

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g007_row000_weighted_charge
