import ElevenSquare.Tasks.T07.CaptureSiteDiamond
import ElevenSquare.Tasks.T07.CaptureBranchGeneric

/-! The strong five-point strict-owned seed for every occupied case-438 cell. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem occupied_has_diamondSeed {S : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩)) :
    ∃ R : Packing 11 S, StateHolds R diamondSeed ∧
      ∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i) := by
  obtain ⟨perm, hcell⟩ := occupied_has_owner_order P hocc
  let Q := relabelPacking P perm
  obtain ⟨R, t, ht, hsame⟩ := Q.exists_chart
  have hchartR : IsCharted R := by
    intro i
    exact ⟨t i, (ht i).1, (ht i).2.1, (ht i).2.2⟩
  have hcellR : ∀ i, ClosedCell (ownerCell i)
      (normalizeCenter (R.squares i).center) := by
    intro i
    rw [← (hsame i).center_eq]
    exact hcell i
  exact ⟨R, diamondSeed_holds R hchartR hcellR, perm, hsame⟩

def diamondFar15State : PoseState := seedFar15 diamondSeed (10 : Owner)
def diamondFar13State : PoseState := seedFar13 diamondSeed (10 : Owner) (9 : Owner)
def diamondFar2State : PoseState := seedFar2 diamondSeed (10 : Owner) (9 : Owner) (2 : Owner)
def diamondNearState : PoseState := seedNear diamondSeed (10 : Owner) (9 : Owner) (2 : Owner)

theorem diamondSeed_isCharted {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P diamondSeed) : IsCharted P := by
  intro i
  obtain ⟨r, _, hrow⟩ := hseed.1 i
  rcases hrow with ⟨_, t, ht0, ht1, _, _, haxis⟩
  exact ⟨t, ht0, ht1, haxis⟩

theorem occupied_has_centered_diamond_branches {S V : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩))
    (hsmall : CenteredPacking P V) :
    ∃ R : Packing 11 S, CenteredPacking R V ∧
      (∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i)) ∧
      (StateHolds R diamondFar15State ∨ StateHolds R diamondFar13State ∨
        StateHolds R diamondFar2State ∨ StateHolds R diamondNearState) := by
  obtain ⟨R, hseed, perm, hsame⟩ := occupied_has_diamondSeed P hocc
  have hcenter : CenteredPacking R V := by
    intro i p hp
    exact hsmall (perm i) p (((hsame i).closed_iff p).mpr hp)
  refine ⟨R, hcenter, ⟨perm, hsame⟩, ?_⟩
  exact state_closed_branch_states R diamondSeed hseed
    (diamondSeed_isCharted R hseed) (10 : Owner) (9 : Owner) (2 : Owner)

end
end ElevenSquare.Tasks.T07
