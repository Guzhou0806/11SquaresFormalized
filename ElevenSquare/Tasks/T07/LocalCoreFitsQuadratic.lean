import ElevenSquare.Tasks.T07.LocalMinkowski
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Strict quadratic certificates on a closed rational interval. The interval
lemma applies to each signed local coordinate of a rotated core vertex. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem quadratic_pos_of_left (a b c L t : ℝ)
    (hL : 0 < Quadratic a b c L) (ht : L ≤ t)
    (hslope : 0 ≤ a * (t + L) + b) :
    0 < Quadratic a b c t := by
  have hterm : 0 ≤ (t - L) * (a * (t + L) + b) :=
    mul_nonneg (sub_nonneg.mpr ht) hslope
  have heq : Quadratic a b c t =
      Quadratic a b c L + (t - L) * (a * (t + L) + b) := by
    dsimp [Quadratic]
    ring
  rw [heq]
  linarith

theorem quadratic_pos_of_right (a b c U t : ℝ)
    (hU : 0 < Quadratic a b c U) (ht : t ≤ U)
    (hslope : a * (t + U) + b ≤ 0) :
    0 < Quadratic a b c t := by
  have hterm : (U - t) * (a * (t + U) + b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht) hslope
  have heq : Quadratic a b c t =
      Quadratic a b c U - (U - t) * (a * (t + U) + b) := by
    dsimp [Quadratic]
    ring
  rw [heq]
  linarith

theorem quadratic_pos_of_discriminant (a b c t : ℝ)
    (ha : 0 < a) (hdisc : 0 < 4 * a * c - b ^ 2) :
    0 < Quadratic a b c t := by
  have hid : 4 * a * Quadratic a b c t =
      (2 * a * t + b) ^ 2 + (4 * a * c - b ^ 2) := by
    dsimp [Quadratic]
    ring
  have hpos : 0 < 4 * a * Quadratic a b c t := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hdisc
  nlinarith only [hpos, ha]

/-- Every alternative is an exact rationally checkable certificate: monotone
from the left, monotone from the right, or positive quadratic discriminant
margin. Endpoints stay strictly inside the physical open square. -/
theorem quadratic_pos_on_Icc (a b c L U t : ℝ)
    (htL : L ≤ t) (htU : t ≤ U)
    (hL : 0 < Quadratic a b c L)
    (hU : 0 < Quadratic a b c U)
    (hcert :
      (0 ≤ a ∧ 0 ≤ 2 * a * L + b) ∨
      (a ≤ 0 ∧ 0 ≤ a * (L + U) + b) ∨
      (0 ≤ a ∧ 2 * a * U + b ≤ 0) ∨
      (a ≤ 0 ∧ a * (L + U) + b ≤ 0) ∨
      (0 < a ∧ 0 < 4 * a * c - b ^ 2)) :
    0 < Quadratic a b c t := by
  rcases hcert with h | h | h | h | h
  · apply quadratic_pos_of_left a b c L t hL htL
    have hm := mul_nonneg h.1 (sub_nonneg.mpr htL)
    nlinarith [h.2]
  · apply quadratic_pos_of_left a b c L t hL htL
    have hm := mul_nonneg (neg_nonneg.mpr h.1) (sub_nonneg.mpr htU)
    nlinarith [h.2]
  · apply quadratic_pos_of_right a b c U t hU htU
    have hm := mul_nonneg h.1 (sub_nonneg.mpr htU)
    nlinarith [h.2]
  · apply quadratic_pos_of_right a b c U t hU htU
    have hm := mul_nonneg (neg_nonneg.mpr h.1) (sub_nonneg.mpr htL)
    nlinarith [h.2]
  · exact quadratic_pos_of_discriminant a b c t h.1 h.2

/-- A signed rotated-coordinate margin with rational coefficients. The value
is positive precisely when that side of the scaled physical core is strict. -/
def signedCoreQuad (x y sign : ℚ) (t : ℝ) : ℝ :=
  Quadratic (((fieldScaleRat - 2 * sign * x : ℚ) : ℝ))
    (((4 * sign * y : ℚ) : ℝ))
    (((fieldScaleRat + 2 * sign * x : ℚ) : ℝ)) t

theorem signedCoreQuad_eq (x y sign : ℚ) (t : ℝ) :
    signedCoreQuad x y sign t = fieldScale * (1 + t ^ 2) +
      (sign : ℝ) * 2 * ((1 - t ^ 2) * (x : ℝ) + 2 * t * (y : ℝ)) := by
  simp only [signedCoreQuad, Quadratic, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat, fieldScaleRat_cast]
  ring

/-- All four signed quadratic margins put a normalized field vertex strictly
inside the actual unit square for every chart angle in the certified range. -/
theorem fieldCoreVertex_open_of_signed_quads (q : UnitSquare) (v : QPoint)
    (t : ℝ) (haxis : q.axis = chartAxis t)
    (hxp : 0 < signedCoreQuad v.1 v.2 1 t)
    (hxm : 0 < signedCoreQuad v.1 v.2 (-1) t)
    (hyp : 0 < signedCoreQuad v.2 (-v.1) 1 t)
    (hym : 0 < signedCoreQuad v.2 (-v.1) (-1) t) :
    OpenSquare q (q.center + realPoint (qpointFieldNormalize v)) := by
  let nx : ℝ := (1 - t ^ 2) * (v.1 : ℝ) + 2 * t * (v.2 : ℝ)
  let ny : ℝ := (1 - t ^ 2) * (v.2 : ℝ) - 2 * t * (v.1 : ℝ)
  let den : ℝ := fieldScale * (1 + t ^ 2)
  have hden : 0 < den := mul_pos fieldScale_pos (by positivity)
  have hxlo : -den / 2 < nx := by
    rw [signedCoreQuad_eq] at hxp
    simp only [Rat.cast_one, one_mul] at hxp
    dsimp [nx, den]
    nlinarith [hxp]
  have hxhi : nx < den / 2 := by
    rw [signedCoreQuad_eq] at hxm
    simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul] at hxm
    dsimp [nx, den]
    nlinarith [hxm]
  have hylo : -den / 2 < ny := by
    rw [signedCoreQuad_eq] at hyp
    simp only [Rat.cast_one, one_mul] at hyp
    dsimp [ny, den]
    simp only [Rat.cast_neg] at hyp
    nlinarith [hyp]
  have hyhi : ny < den / 2 := by
    rw [signedCoreQuad_eq] at hym
    simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul] at hym
    dsimp [ny, den]
    nlinarith [hym]
  have hxloc : localX q (q.center + realPoint (qpointFieldNormalize v)) =
      nx / den := by
    rw [realPoint_qpointFieldNormalize]
    dsimp [localX, dot, realPoint, fieldPhysical]
    rw [haxis]
    dsimp [chartAxis, nx, den]
    have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [fieldScale_ne_zero, hd]
    ring
  have hyloc : localY q (q.center + realPoint (qpointFieldNormalize v)) =
      ny / den := by
    rw [realPoint_qpointFieldNormalize]
    dsimp [localY, dot, perp, realPoint, fieldPhysical]
    rw [haxis]
    dsimp [chartAxis, ny, den]
    have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [fieldScale_ne_zero, hd]
    ring
  rw [OpenSquare, hxloc, hyloc]
  constructor
  · apply abs_lt.mpr
    constructor
    · have hl := (div_lt_iff hden).mpr (show -nx < (1 / 2 : ℝ) * den by linarith)
      rw [neg_div] at hl
      linarith
    · exact (div_lt_iff hden).mpr (by linarith [hxhi])
  · apply abs_lt.mpr
    constructor
    · have hl := (div_lt_iff hden).mpr (show -ny < (1 / 2 : ℝ) * den by linarith)
      rw [neg_div] at hl
      linarith
    · exact (div_lt_iff hden).mpr (by linarith [hyhi])

end
end ElevenSquare.Tasks.T07
