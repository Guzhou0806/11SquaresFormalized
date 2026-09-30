import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 4. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter40Coeffs : Fin 8 → ℚ := ![(1/4), (-37/16), (5/2), (-35/16), -4, (-15/16), (15/4), (-25/16)]

theorem nearCenter40_poly :
    (constructionCenter 4).1 - T/2 = polynomialAt nearCenter40Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter40Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter40Lo : ℝ := (-438541795011407089/1000000000000000000)
def nearCenter40Hi : ℝ := (-27408862188212943/62500000000000000)

theorem nearCenter40_bounds :
    nearCenter40Lo ≤ (constructionCenter 4).1 - T/2 ∧
    (constructionCenter 4).1 - T/2 ≤ nearCenter40Hi := by
  have hp := polynomial_interval nearCenter40Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter40Lo ≤
      polynomialLower nearCenter40Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter40Lo, polynomialLower, nearCenter40Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter40Coeffs nearRootLo nearRootHi ≤
      nearCenter40Hi := by
    norm_num [nearCenter40Hi, polynomialUpper, nearCenter40Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter40_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter41Coeffs : Fin 8 → ℚ := ![(3/4), (37/16), (-5/2), (35/16), 4, (15/16), (-15/4), (25/16)]

theorem nearCenter41_poly :
    (constructionCenter 4).2 - T/2 = polynomialAt nearCenter41Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter41Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter41Lo : ℝ := (89908862188212943/62500000000000000)
def nearCenter41Hi : ℝ := (1438541795011407089/1000000000000000000)

theorem nearCenter41_bounds :
    nearCenter41Lo ≤ (constructionCenter 4).2 - T/2 ∧
    (constructionCenter 4).2 - T/2 ≤ nearCenter41Hi := by
  have hp := polynomial_interval nearCenter41Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter41Lo ≤
      polynomialLower nearCenter41Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter41Lo, polynomialLower, nearCenter41Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter41Coeffs nearRootLo nearRootHi ≤
      nearCenter41Hi := by
    norm_num [nearCenter41Hi, polynomialUpper, nearCenter41Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter41_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
