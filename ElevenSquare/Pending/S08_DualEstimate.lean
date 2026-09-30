import ElevenSquare.Pending.Types
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite dual residual estimates and an attained normalized radius. -/

namespace ElevenSquare.Pending
noncomputable section

-- The derivative matrix may be algebraic. The dual vector is exact rational data.
theorem dual_signed_coordinate_bound
    (A : Fin 42 → Fin 33 → ℝ) (weights K : Fin 42 → ℝ)
    (h : Displacement) (j : Fin 33) (σ ε τ R : ℝ)
    (hweights : ∀ i, 0 ≤ weights i) (hε : 0 ≤ ε) (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (hbox : ∀ k, |h k| ≤ τ*R)
    (hrows : ∀ i, -(τ^2*K i/2) ≤ LinearForm (A i) h)
    (hresidual : (∑ k, |(∑ i, weights i*A i k)-(if k=j then σ else 0)|) ≤ ε) :
    -(σ*h j) ≤ ε*τ*R + τ^2*(∑ i, weights i*K i)/2 := by
  let B : Fin 33 → ℝ := fun k => ∑ i, weights i*A i k
  let E : Fin 33 → ℝ := fun k => B k - (if k=j then σ else 0)
  have weighted : ∑ i, weights i * LinearForm (A i) h = LinearForm B h := by
    simp only [LinearForm, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have lower : -(τ^2*(∑ i, weights i*K i)/2) ≤ LinearForm B h := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (hweights i))
    have heq : (∑ i, weights i * (-(τ^2*K i/2))) =
        -(τ^2*(∑ i, weights i*K i)/2) := by
      calc
        _ = ∑ i, (-τ^2/2)*(weights i*K i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (-τ^2/2)*(∑ i, weights i*K i) := (Finset.mul_sum ..).symm
        _ = _ := by ring
    rw [heq, weighted] at hsum
    exact hsum
  have error_bound : LinearForm E h ≤ ε*τ*R := by
    calc
      _ ≤ ∑ k, |E k| *(τ*R) := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          E k*h k ≤ |E k*h k| := le_abs_self _
          _ = |E k| *|h k| := abs_mul _ _
          _ ≤ |E k| *(τ*R) := mul_le_mul_of_nonneg_left (hbox k) (abs_nonneg _)
      _ = (∑ k, |E k|)*(τ*R) := (Finset.sum_mul ..).symm
      _ ≤ ε*(τ*R) := mul_le_mul_of_nonneg_right hresidual (mul_nonneg hτ hR)
      _ = _ := by ring
  have identity : LinearForm E h = LinearForm B h - σ*h j := by
    simp [LinearForm, E, sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [identity] at error_bound
  linarith

theorem strict_dual_contradiction (τ r ε R M : ℝ)
    (hτ : 0 < τ ∧ τ ≤ 1) (hr : 0 < r) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hstrict : M < 2*(r-ε*R))
    (hbound : τ*r ≤ ε*τ*R + τ^2*M/2) : False := by
  have hm : τ^2*M ≤ τ*M := by
    nlinarith [mul_nonneg (mul_nonneg hτ.1.le (sub_nonneg.mpr hτ.2)) hM]
  have hstrict' := mul_lt_mul_of_pos_left hstrict hτ.1
  nlinarith

theorem normalized_radius_attained (r : Fin 33 → ℝ) (h : Displacement)
    (hr : ∀ j, 0 < r j) (hrect : InRectangle r h) (hnz : h ≠ 0) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ (∀ j, |h j| ≤ τ*r j) ∧
      ∃ j, |h j| = τ*r j := by
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j : Fin 33 => |h j|/r j)
  let τ := |h j|/r j
  have hupper : τ ≤ 1 := (div_le_one (hr j)).mpr (hrect j)
  have hpos : 0 < τ := by
    by_contra hn
    have hzero : h = 0 := by
      funext k
      have hk : |h k|/r k ≤ 0 := le_trans (hj k) (le_of_not_gt hn)
      have hk' : |h k| ≤ 0 := by
        simpa using (div_le_iff₀ (hr k)).mp hk
      exact abs_eq_zero.mp (le_antisymm hk' (abs_nonneg _))
    exact hnz hzero
  refine ⟨τ, hpos, hupper, ?_, j, ?_⟩
  · intro k
    exact (div_le_iff₀ (hr k)).mp (hj k)
  · exact (div_mul_cancel₀ (|h j|) (ne_of_gt (hr j))).symm


end
end ElevenSquare.Pending
