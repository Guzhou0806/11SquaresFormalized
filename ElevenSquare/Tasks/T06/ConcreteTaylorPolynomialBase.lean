import ElevenSquare.Tasks.T06.PolynomialBounds
import Mathlib.Tactic.NormNum

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section

theorem concrete_poly_abs_bound (c : Fin 8 → ℚ) (m : ℚ)
    (hl : -m ≤ polyLower c (365769307604/1000000000000)
      (365769307605/1000000000000))
    (hu : polyUpper c (365769307604/1000000000000)
      (365769307605/1000000000000) ≤ m) :
    |polyEval c u| ≤ (m : ℝ) := by
  have ha : ((365769307604/1000000000000 : ℚ) : ℝ) ≤ u := by
    have h := u_bounds.1
    norm_num [rootLo] at h ⊢
    linarith
  have hb : u ≤ ((365769307605/1000000000000 : ℚ) : ℝ) := by
    have h := u_bounds.2
    norm_num [rootHi] at h ⊢
    linarith
  obtain ⟨hl', hu'⟩ := poly_enclosure c (365769307604/1000000000000)
    (365769307605/1000000000000) u (by norm_num) ha hb
  have hlo : -(m : ℝ) ≤ (polyLower c (365769307604/1000000000000)
      (365769307605/1000000000000) : ℝ) := by exact_mod_cast hl
  have hhi : (polyUpper c (365769307604/1000000000000)
      (365769307605/1000000000000) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hu
  exact abs_le.mpr ⟨hlo.trans hl', hu'.trans hhi⟩

theorem concrete_poly_upper_bound (c : Fin 8 → ℚ) (m : ℚ)
    (hu : polyUpper c (365769307604/1000000000000)
      (365769307605/1000000000000) ≤ m) :
    polyEval c u ≤ (m : ℝ) := by
  have ha : ((365769307604/1000000000000 : ℚ) : ℝ) ≤ u := by
    have h := u_bounds.1
    norm_num [rootLo] at h ⊢
    linarith
  have hb : u ≤ ((365769307605/1000000000000 : ℚ) : ℝ) := by
    have h := u_bounds.2
    norm_num [rootHi] at h ⊢
    linarith
  have h := (poly_enclosure c (365769307604/1000000000000)
    (365769307605/1000000000000) u (by norm_num) ha hb).2
  exact h.trans (by exact_mod_cast hu)

end
end ElevenSquare.Tasks.T06
