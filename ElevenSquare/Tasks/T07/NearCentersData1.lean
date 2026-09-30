import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 1. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter10Coeffs : Fin 8 → ℚ := ![(3/4), (37/16), (-5/2), (35/16), 4, (15/16), (-15/4), (25/16)]

theorem nearCenter10_poly :
    (constructionCenter 1).1 - T/2 = polynomialAt nearCenter10Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter10Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter10Lo : ℝ := (89908862188212943/62500000000000000)
def nearCenter10Hi : ℝ := (1438541795011407089/1000000000000000000)

theorem nearCenter10_bounds :
    nearCenter10Lo ≤ (constructionCenter 1).1 - T/2 ∧
    (constructionCenter 1).1 - T/2 ≤ nearCenter10Hi := by
  have hp := polynomial_interval nearCenter10Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter10Lo ≤
      polynomialLower nearCenter10Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter10Lo, polynomialLower, nearCenter10Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter10Coeffs nearRootLo nearRootHi ≤
      nearCenter10Hi := by
    norm_num [nearCenter10Hi, polynomialUpper, nearCenter10Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter10_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter11Coeffs : Fin 8 → ℚ := ![(-3/4), (-37/16), (5/2), (-35/16), -4, (-15/16), (15/4), (-25/16)]

theorem nearCenter11_poly :
    (constructionCenter 1).2 - T/2 = polynomialAt nearCenter11Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter11Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter11Lo : ℝ := (-1438541795011407089/1000000000000000000)
def nearCenter11Hi : ℝ := (-89908862188212943/62500000000000000)

theorem nearCenter11_bounds :
    nearCenter11Lo ≤ (constructionCenter 1).2 - T/2 ∧
    (constructionCenter 1).2 - T/2 ≤ nearCenter11Hi := by
  have hp := polynomial_interval nearCenter11Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter11Lo ≤
      polynomialLower nearCenter11Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter11Lo, polynomialLower, nearCenter11Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter11Coeffs nearRootLo nearRootHi ≤
      nearCenter11Hi := by
    norm_num [nearCenter11Hi, polynomialUpper, nearCenter11Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter11_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
