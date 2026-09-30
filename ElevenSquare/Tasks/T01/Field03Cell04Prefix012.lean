import ElevenSquare.Tasks.T01.Field03Cell04Chain
import ElevenSquare.Tasks.T01.Field03Cell04Row010.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row011.PackingCapture

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- First twelve adjacent closed intervals, from zero through 3/64. -/
theorem field03_cell04_capture_first_twelve (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (t : ℝ) (ht0 : 0 ≤ t) (htop : t ≤ (3/64 : ℝ))
    (ha : (P.squares i).axis = chartAxis t) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  let M : ℝ → Prop := fun x => (P.squares i).axis = chartAxis x →
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i)
  have h11 : ∀ x, 0 ≤ x → x ≤ (11/256 : ℝ) → M x := by
    apply field03_closed_interval_append M (5/128) (11/256)
    · intro x hx0 hxmid hax
      exact field03_cell04_capture_first_ten P i j hij hcell hother hchart x hx0 hxmid hax
    · intro x hxlo hxhi hax
      exact Field03Cell04Row010.capture_from_packing P i j hij hcell hother hchart
        x (by linarith) (by linarith) hax hxlo hxhi
  have h12 : ∀ x, 0 ≤ x → x ≤ (3/64 : ℝ) → M x := by
    apply field03_closed_interval_append M (11/256) (3/64) h11
    intro x hxlo hxhi hax
    exact Field03Cell04Row011.capture_from_packing P i j hij hcell hother hchart
      x (by linarith) (by linarith) hax hxlo hxhi
  exact h12 t ht0 htop ha

end
end ElevenSquare.Tasks.T01
