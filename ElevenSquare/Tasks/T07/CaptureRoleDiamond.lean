import ElevenSquare.Tasks.T07.CaptureDiamondBranches
import ElevenSquare.Tasks.T07.CaptureDiamondSource

/-! The five-point seed in the construction's role order. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def roleDiamondSeed : PoseState where
  rows i := diamondSeed.rows (roleOwner i)
  owned i := diamondSeed.owned (roleOwner i)

theorem roleDiamondSeed_cell (i : Owner) :
    roleDiamondSeed.rows i =
      [{ lo := 0, hi := 1, centers := seedCellPolygon (roleCell i) }] ∧
    roleDiamondSeed.owned i = physicalSiteDiamond (roleCell i) := by
  rw [← role_cell_correspondence]
  exact ⟨rfl, rfl⟩

theorem roleDiamondSeed_holds {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P diamondSeed) :
    StateHolds (relabelPacking P rolePermutation) roleDiamondSeed := by
  constructor
  · intro i
    exact hseed.1 (roleOwner i)
  · intro i
    exact hseed.2 (roleOwner i)

theorem occupied_has_centered_roleDiamondSeed {S V : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩))
    (hsmall : CenteredPacking P V) :
    ∃ R : Packing 11 S, CenteredPacking R V ∧ StateHolds R roleDiamondSeed ∧
      ∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i) := by
  obtain ⟨Q, hseed, perm, hsame⟩ := occupied_has_diamondSeed P hocc
  let R := relabelPacking Q rolePermutation
  let permRole : Equiv.Perm Owner := rolePermutation.trans perm
  refine ⟨R, ?_, roleDiamondSeed_holds Q hseed, permRole, ?_⟩
  · intro i p hp
    exact hsmall (perm (roleOwner i)) p
      (((hsame (roleOwner i)).closed_iff p).mpr hp)
  · intro i
    exact hsame (roleOwner i)

/-- The capture guards are role 1 (cell 15), role 10 (cell 13), and role 6
(cell 2) after the construction-role permutation. -/
theorem roleDiamond_guard_cells :
    roleCell (1 : Owner) = 15 ∧
    roleCell (10 : Owner) = 13 ∧
    roleCell (6 : Owner) = 2 := by decide

def roleDiamondFar15State : PoseState := seedFar15 roleDiamondSeed (1 : Owner)
def roleDiamondFar13State : PoseState :=
  seedFar13 roleDiamondSeed (1 : Owner) (10 : Owner)
def roleDiamondFar2State : PoseState :=
  seedFar2 roleDiamondSeed (1 : Owner) (10 : Owner) (6 : Owner)
def roleDiamondNearState : PoseState :=
  seedNear roleDiamondSeed (1 : Owner) (10 : Owner) (6 : Owner)

theorem roleDiamondSeed_isCharted {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P roleDiamondSeed) : IsCharted P := by
  intro i
  obtain ⟨r, _, hrow⟩ := hseed.1 i
  rcases hrow with ⟨_, t, ht0, ht1, _, _, haxis⟩
  exact ⟨t, ht0, ht1, haxis⟩

theorem roleDiamond_closed_branches {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P roleDiamondSeed) :
    StateHolds P roleDiamondFar15State ∨ StateHolds P roleDiamondFar13State ∨
      StateHolds P roleDiamondFar2State ∨ StateHolds P roleDiamondNearState := by
  exact state_closed_branch_states P roleDiamondSeed hseed
    (roleDiamondSeed_isCharted P hseed) (1 : Owner) (10 : Owner) (6 : Owner)

theorem roleDiamondNear_of_far_terminal_traces {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P roleDiamondSeed)
    (far15 : ∃ s, VerifiedTrace roleDiamondFar15State s ∧ Terminal s)
    (far13 : ∃ s, VerifiedTrace roleDiamondFar13State s ∧ Terminal s)
    (far2 : ∃ s, VerifiedTrace roleDiamondFar2State s ∧ Terminal s) :
    StateHolds P roleDiamondNearState := by
  rcases roleDiamond_closed_branches P hseed with h | h | h | h
  · obtain ⟨s, trace, terminal⟩ := far15
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far13
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far2
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · exact h

end
end ElevenSquare.Tasks.T07
