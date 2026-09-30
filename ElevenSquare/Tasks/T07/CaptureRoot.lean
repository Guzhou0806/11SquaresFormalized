import ElevenSquare.Pending.S05_Trace
import ElevenSquare.Orientation
import ElevenSquare.Cover

/-! A chart-complete starting state for case-438 trace certificates. Every
physical packing can be represented in the closed half-angle chart, including
both endpoint orientations, before geometric pruning begins. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- The first semantic trace state imposes only the closed half-angle chart.
Its empty owned hull makes no unverified ownership assertion. -/
def chartRoot : PoseState where
  rows _ := [{ lo := 0, hi := 1, centers := [] }]
  owned _ := []

theorem chartRoot_holds {S : ℝ} (P : Packing 11 S) (h : IsCharted P) :
    StateHolds P chartRoot := by
  constructor
  · intro i
    obtain ⟨t, ht0, ht1, haxis⟩ := h i
    refine ⟨{ lo := 0, hi := 1, centers := [] }, by simp [chartRoot], ?_⟩
    refine ⟨?_, t, ht0, ht1, ?_, ?_, haxis⟩
    · simp [Polygon.carrier]
    · simpa using ht0
    · simpa using ht1
  · intro i
    simp [chartRoot, rationalHull]

/-- The chart choice changes only representatives, never physical squares. -/
theorem packing_has_chartRoot {S : ℝ} (P : Packing 11 S) :
    ∃ R : Packing 11 S,
      (∀ i, SameSquare (P.squares i) (R.squares i)) ∧
      StateHolds R chartRoot := by
  obtain ⟨R, t, ht, hsame⟩ := P.exists_chart
  refine ⟨R, hsame, chartRoot_holds R ?_⟩
  intro i
  refine ⟨t i, (ht i).1, (ht i).2.1, ?_⟩
  exact (ht i).2.2

/-- Replacing axes by equivalent chart representatives preserves the exact
occupied-cell antecedent because every center is unchanged. -/
theorem chart_representative_occupies {S : ℝ} {P R : Packing 11 S}
    (hsame : ∀ i, SameSquare (P.squares i) (R.squares i))
    {m : Finset (Fin 16)} (hocc : Occupies P m) : Occupies R m := by
  obtain ⟨a, ha, him, hcell⟩ := hocc
  refine ⟨a, ha, him, ?_⟩
  intro i
  rw [← (hsame i).center_eq]
  exact hcell i

theorem chartRoot_trace_sound {S : ℝ} (P : Packing 11 S)
    (h : IsCharted P) {s : PoseState}
    (trace : VerifiedTrace chartRoot s) : StateHolds P s :=
  verified_trace_sound P (chartRoot_holds P h) trace

theorem chartRoot_terminal_impossible {S : ℝ} (P : Packing 11 S)
    (h : IsCharted P) {s : PoseState}
    (trace : VerifiedTrace chartRoot s) (terminal : Terminal s) : False :=
  terminal_contradiction P s (chartRoot_trace_sound P h trace) terminal

end
end ElevenSquare.Tasks.T07
