import ElevenSquare.Tasks.T07.CaptureBranchGeneric
import ElevenSquare.Tasks.T07.CaptureSeed

/-! The four closed capture branches based on the actual occupied case-438
Voronoi cells. The archived phase-2 initial owned hulls and finer pose covers
require subsequent verified promotions and prunes; they are not this seed. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def seedFar15State : PoseState := seedFar15 occupiedCellSeed (10 : Owner)
def seedFar13State : PoseState := seedFar13 occupiedCellSeed (10 : Owner) (9 : Owner)
def seedFar2State : PoseState := seedFar2 occupiedCellSeed (10 : Owner) (9 : Owner) (2 : Owner)
def seedNearState : PoseState := seedNear occupiedCellSeed (10 : Owner) (9 : Owner) (2 : Owner)

theorem seed_branch_owner_cells :
    ownerCell (10 : Owner) = 15 ∧
    ownerCell (9 : Owner) = 13 ∧
    ownerCell (2 : Owner) = 2 := by
  decide

theorem occupied_seed_isCharted {S : ℝ} (P : Packing 11 S)
    (hs : StateHolds P occupiedCellSeed) : IsCharted P := by
  intro i
  obtain ⟨r, _, hrow⟩ := hs.1 i
  rcases hrow with ⟨_, t, ht0, ht1, _, _, haxis⟩
  exact ⟨t, ht0, ht1, haxis⟩

theorem seeded_closed_branch_states {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P occupiedCellSeed) :
    StateHolds P seedFar15State ∨ StateHolds P seedFar13State ∨
      StateHolds P seedFar2State ∨ StateHolds P seedNearState := by
  exact state_closed_branch_states P occupiedCellSeed hseed
    (occupied_seed_isCharted P hseed) (10 : Owner) (9 : Owner) (2 : Owner)

theorem occupied_has_seeded_branch {S : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩)) :
    ∃ R : Packing 11 S, (∃ perm : Equiv.Perm Owner,
      ∀ i, SameSquare (P.squares (perm i)) (R.squares i)) ∧
      (StateHolds R seedFar15State ∨ StateHolds R seedFar13State ∨
        StateHolds R seedFar2State ∨ StateHolds R seedNearState) := by
  obtain ⟨R, hseed, perm, hsame⟩ := occupied_has_seed P hocc
  exact ⟨R, ⟨perm, hsame⟩, seeded_closed_branch_states R hseed⟩

/-- The seed construction preserves a smaller centered container, which is
needed when the local packet is transported into side `T`. -/
theorem occupied_has_centered_seeded_branch {S V : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩))
    (hsmall : CenteredPacking P V) :
    ∃ R : Packing 11 S, CenteredPacking R V ∧
      (∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i)) ∧
      (StateHolds R seedFar15State ∨ StateHolds R seedFar13State ∨
        StateHolds R seedFar2State ∨ StateHolds R seedNearState) := by
  obtain ⟨R, hseed, perm, hsame⟩ := occupied_has_seed P hocc
  refine ⟨R, ?_, ⟨perm, hsame⟩, seeded_closed_branch_states R hseed⟩
  intro i p hp
  exact hsmall (perm i) p (((hsame i).closed_iff p).mpr hp)

/-- A source trace must begin at one of the seeded branch states above. -/
theorem seeded_near_of_far_terminal_traces {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P occupiedCellSeed)
    (far15 : ∃ s, VerifiedTrace seedFar15State s ∧ Terminal s)
    (far13 : ∃ s, VerifiedTrace seedFar13State s ∧ Terminal s)
    (far2 : ∃ s, VerifiedTrace seedFar2State s ∧ Terminal s) :
    StateHolds P seedNearState := by
  rcases seeded_closed_branch_states P hseed with h | h | h | h
  · obtain ⟨s, trace, terminal⟩ := far15
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far13
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far2
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · exact h

end
end ElevenSquare.Tasks.T07
