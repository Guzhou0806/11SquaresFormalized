import ElevenSquare.Tasks.T07.CaptureBranchGeneric
import ElevenSquare.Tasks.T07.ShortcutSiteReduction

/-! The four closed capture branches from the exact Voronoi seed. Each branch
retains one rational point strictly inside every occupied square. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def siteFar15State : PoseState := seedFar15 siteSeed (10 : Owner)
def siteFar13State : PoseState := seedFar13 siteSeed (10 : Owner) (9 : Owner)
def siteFar2State : PoseState := seedFar2 siteSeed (10 : Owner) (9 : Owner) (2 : Owner)
def siteNearState : PoseState := seedNear siteSeed (10 : Owner) (9 : Owner) (2 : Owner)

theorem siteSeed_isCharted {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P siteSeed) : IsCharted P := by
  intro i
  obtain ⟨r, _, hrow⟩ := hseed.1 i
  rcases hrow with ⟨_, t, ht0, ht1, _, _, haxis⟩
  exact ⟨t, ht0, ht1, haxis⟩

theorem siteSeed_closed_branches {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P siteSeed) :
    StateHolds P siteFar15State ∨ StateHolds P siteFar13State ∨
      StateHolds P siteFar2State ∨ StateHolds P siteNearState := by
  exact state_closed_branch_states P siteSeed hseed
    (siteSeed_isCharted P hseed) (10 : Owner) (9 : Owner) (2 : Owner)

theorem occupied_has_centered_site_branches {S V : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩))
    (hsmall : CenteredPacking P V) :
    ∃ R : Packing 11 S, CenteredPacking R V ∧
      (∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i)) ∧
      (StateHolds R siteFar15State ∨ StateHolds R siteFar13State ∨
        StateHolds R siteFar2State ∨ StateHolds R siteNearState) := by
  obtain ⟨R, hseed, hcenter, perm, hsame⟩ :=
    occupied_has_siteSeed_centered P hocc hsmall
  exact ⟨R, hcenter, ⟨perm, hsame⟩, siteSeed_closed_branches R hseed⟩

/-- Concrete terminal traces from the three far branches would leave every
occupied packing in the near branch, with the strict seed ownership intact. -/
theorem siteNear_of_far_terminal_traces {S : ℝ} (P : Packing 11 S)
    (hseed : StateHolds P siteSeed)
    (far15 : ∃ s, VerifiedTrace siteFar15State s ∧ Terminal s)
    (far13 : ∃ s, VerifiedTrace siteFar13State s ∧ Terminal s)
    (far2 : ∃ s, VerifiedTrace siteFar2State s ∧ Terminal s) :
    StateHolds P siteNearState := by
  rcases siteSeed_closed_branches P hseed with h | h | h | h
  · obtain ⟨s, trace, terminal⟩ := far15
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far13
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far2
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · exact h

end
end ElevenSquare.Tasks.T07
