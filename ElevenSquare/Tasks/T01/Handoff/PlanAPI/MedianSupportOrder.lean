import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Defs

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI

/-- A lower median certificate: fewer than `k` of the sites project below `b`.
This avoids choosing a particular order statistic when projections tie. -/
def MedianLowerBound {α β : Type*} [DecidableEq α] [LinearOrder β]
    (sites : Finset α) (k : ℕ) (projection : α → β) (b : β) : Prop :=
  (sites.filter (fun p => projection p < b)).card < k

/-- Every `k`-subset contains a site whose projection reaches a certified
lower median bound. This is the combinatorial step needed to pass from one
median support inequality to every `k`-subset hull support inequality. -/
theorem median_lower_bound_hits_subset {α β : Type*} [DecidableEq α]
    [LinearOrder β] (sites subset : Finset α) (k : ℕ)
    (projection : α → β) (b : β)
    (hmedian : MedianLowerBound sites k projection b)
    (hsubset : subset ⊆ sites) (hcard : subset.card = k) :
    ∃ p ∈ subset, b ≤ projection p := by
  classical
  by_contra hnone
  have hsmall : subset ⊆ sites.filter (fun p => projection p < b) := by
    intro p hp
    have hlt : projection p < b := by
      apply lt_of_not_ge
      intro hge
      exact hnone ⟨p, hp, hge⟩
    simp [hsubset hp, hlt]
  have hle := Finset.card_le_card hsmall
  exact (Nat.not_le_of_gt hmedian) (by simpa [hcard] using hle)

/-- A certified median support bound implies the corresponding support
inequality for each `k`-subset, using one of its sites as a witness. -/
theorem median_support_of_lower_bound {α β : Type*} [DecidableEq α]
    [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] (sites subset : Finset α) (k : ℕ)
    (projection : α → β) (b center coreSupport : β)
    (hmedian : MedianLowerBound sites k projection b)
    (hsubset : subset ⊆ sites) (hcard : subset.card = k)
    (hcenter : center ≤ b + coreSupport) :
    ∃ p ∈ subset, center ≤ projection p + coreSupport := by
  obtain ⟨p, hp, hprojection⟩ :=
    median_lower_bound_hits_subset sites subset k projection b
      hmedian hsubset hcard
  exact ⟨p, hp, hcenter.trans (add_le_add hprojection le_rfl)⟩

end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.median_support_of_lower_bound
