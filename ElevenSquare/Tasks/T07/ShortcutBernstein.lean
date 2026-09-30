import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! A reusable rational interval certificate for the quadratic expressions
obtained by clearing the positive denominator of the half-angle chart.
The three Bernstein coefficients are exact rational calculations when the
input coefficients and interval endpoints are rational. A producer may split
an interval until the middle coefficient is nonnegative; no sampling is used. -/
namespace ElevenSquare.Tasks.T07
noncomputable section

def quadraticAt (A B C t : ℝ) : ℝ := A*t^2+B*t+C

def quadraticBernsteinMiddle (A B C a b : ℝ) : ℝ :=
  quadraticAt A B C a + (b-a)*(2*A*a+B)/2

theorem quadratic_bernstein_identity (A B C a b u : ℝ) :
    quadraticAt A B C (a+(b-a)*u) =
      quadraticAt A B C a*(1-u)^2 +
      2*quadraticBernsteinMiddle A B C a b*u*(1-u) +
      quadraticAt A B C b*u^2 := by
  dsimp [quadraticAt, quadraticBernsteinMiddle]
  ring

/-- Endpoint positivity and a nonnegative middle Bernstein coefficient
certify a strict inequality on the *whole closed interval*. -/
theorem quadratic_bernstein_pos (A B C a b u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ha : 0 < quadraticAt A B C a)
    (hm : 0 ≤ quadraticBernsteinMiddle A B C a b)
    (hb : 0 < quadraticAt A B C b) :
    0 < quadraticAt A B C (a+(b-a)*u) := by
  rw [quadratic_bernstein_identity]
  rcases lt_or_eq_of_le hu1 with hlt | heq
  · have hfront : 0 < quadraticAt A B C a*(1-u)^2 :=
      mul_pos ha (sq_pos_of_pos (by linarith))
    have hmiddle : 0 ≤ 2*quadraticBernsteinMiddle A B C a b*u*(1-u) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm) hu0)
        (by linarith)
    have hlast : 0 ≤ quadraticAt A B C b*u^2 :=
      mul_nonneg hb.le (sq_nonneg _)
    linarith
  · subst u
    norm_num
    exact hb

theorem quadratic_bernstein_pos_on (A B C a b t : ℝ)
    (hab : a < b) (hat : a ≤ t) (htb : t ≤ b)
    (ha : 0 < quadraticAt A B C a)
    (hm : 0 ≤ quadraticBernsteinMiddle A B C a b)
    (hb : 0 < quadraticAt A B C b) :
    0 < quadraticAt A B C t := by
  let u := (t-a)/(b-a)
  have hba : 0 < b-a := sub_pos.mpr hab
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hat) hba.le
  have hu1 : u ≤ 1 := (div_le_one hba).mpr (by linarith)
  have ht : a+(b-a)*u = t := by
    dsimp [u]
    field_simp [ne_of_gt hba]
  rw [← ht]
  exact quadratic_bernstein_pos A B C a b u hu0 hu1 ha hm hb

end
end ElevenSquare.Tasks.T07
