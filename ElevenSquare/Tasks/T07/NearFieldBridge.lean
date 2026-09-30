import ElevenSquare.Tasks.T07.NearAlgebra

/-! Turning a field-coordinate rectangle into coordinatewise local-center
deviations. These lemmas include the exact cap-to-endpoint translation. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare
noncomputable section

theorem field_rectangle_local_x {p : Point} {lx hx ly hy c cl ch r : ℝ}
    (hp : inRect lx hx ly hy p)
    (hc : cl ≤ c-T/2 ∧ c-T/2 ≤ ch)
    (hl : ch-r ≤ ly/fieldScale-coverCap/2)
    (hr : hy/fieldScale-coverCap/2 ≤ cl+r) :
    |(fieldToLocal p).1-c| ≤ r := by
  obtain ⟨_, _, hyl, hyh⟩ := hp
  have hdivl := div_le_div_of_nonneg_right hyl fieldScale_pos.le
  have hdivh := div_le_div_of_nonneg_right hyh fieldScale_pos.le
  apply abs_le.mpr
  constructor <;> dsimp only [fieldToLocal] <;> linarith

theorem field_rectangle_local_y {p : Point} {lx hx ly hy c cl ch r : ℝ}
    (hp : inRect lx hx ly hy p)
    (hc : cl ≤ c-T/2 ∧ c-T/2 ≤ ch)
    (hl : ch-r ≤ coverCap/2-hx/fieldScale)
    (hr : coverCap/2-lx/fieldScale ≤ cl+r) :
    |(fieldToLocal p).2-c| ≤ r := by
  obtain ⟨hxl, hxh, _, _⟩ := hp
  have hdivl := div_le_div_of_nonneg_right hxl fieldScale_pos.le
  have hdivh := div_le_div_of_nonneg_right hxh fieldScale_pos.le
  apply abs_le.mpr
  constructor <;> dsimp only [fieldToLocal] <;> linarith

end
end ElevenSquare.Tasks.T07
