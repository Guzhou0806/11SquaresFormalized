import ElevenSquare.Tasks.T01.Field03Cell04Prefix016
import ElevenSquare.Tasks.T01.Field03Cell04Row016.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Chain

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Checked only when imported row proofs and this theorem are compiled. -/
theorem field03_cell04_capture_prefix_017 (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ (P.squares j).axis = chartAxis u)
    (t : ℝ) (ht0 : 0 ≤ t) (htop : t ≤ ((11/128) : ℝ))
    (ha : (P.squares i).axis = chartAxis t) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  let M : ℝ → Prop := fun x => (P.squares i).axis = chartAxis x →
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i)
  have h : ∀ x, 0 ≤ x → x ≤ ((11/128) : ℝ) → M x := by
    apply field03_closed_interval_append M (5/64) (11/128)
    · intro x hx0 hxmid hax
      exact field03_cell04_capture_prefix_016 P i j hij hcell hother hchart x hx0 hxmid hax
    · intro x hxlo hxhi hax
      exact Field03Cell04Row016.capture_from_packing P i j hij hcell hother hchart
        x (by linarith) (by linarith) hax hxlo hxhi
  exact h t ht0 htop ha

end
end ElevenSquare.Tasks.T01
