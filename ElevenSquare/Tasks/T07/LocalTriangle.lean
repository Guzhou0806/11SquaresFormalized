import ElevenSquare.Pending.Types
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FinCases

/-! A finite three-point witness for rational hull membership.  Generated
polygon certificates can supply affine weights using exact linear arithmetic. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem rationalHull_of_barycentric3 {vs : List QPoint}
    {a b c : QPoint} {p : Point}
    (ha : a ∈ vs) (hb : b ∈ vs) (hc : c ∈ vs)
    (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1)
    (hpoint : α • realPoint a + β • realPoint b + γ • realPoint c = p) :
    p ∈ rationalHull vs := by
  let w : Fin 3 → ℝ := ![α, β, γ]
  let z : Fin 3 → Point := ![realPoint a, realPoint b, realPoint c]
  apply mem_convexHull_of_exists_fintype w z
  · intro i
    fin_cases i <;> simp [w, hα, hβ, hγ]
  · simpa [w, Fin.sum_univ_succ, add_assoc] using hsum
  · intro i
    fin_cases i
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
    · exact ⟨c, hc, rfl⟩
  · simpa [w, z, Fin.sum_univ_succ, add_assoc] using hpoint

end
end ElevenSquare.Tasks.T07
