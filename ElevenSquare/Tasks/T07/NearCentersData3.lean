import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 3. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter30Coeffs : Fin 8 → ℚ := ![(-3/4), (-37/16), (5/2), (-35/16), -4, (-15/16), (15/4), (-25/16)]

theorem nearCenter30_poly :
    (constructionCenter 3).1 - T/2 = polynomialAt nearCenter30Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter30Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter30Lo : ℝ := (-1438541795011407089/1000000000000000000)
def nearCenter30Hi : ℝ := (-89908862188212943/62500000000000000)

theorem nearCenter30_bounds :
    nearCenter30Lo ≤ (constructionCenter 3).1 - T/2 ∧
    (constructionCenter 3).1 - T/2 ≤ nearCenter30Hi := by
  have hp := polynomial_interval nearCenter30Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter30Lo ≤
      polynomialLower nearCenter30Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter30Lo, polynomialLower, nearCenter30Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter30Coeffs nearRootLo nearRootHi ≤
      nearCenter30Hi := by
    norm_num [nearCenter30Hi, polynomialUpper, nearCenter30Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter30_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter31Coeffs : Fin 8 → ℚ := ![(3/4), (37/16), (-5/2), (35/16), 4, (15/16), (-15/4), (25/16)]

theorem nearCenter31_poly :
    (constructionCenter 3).2 - T/2 = polynomialAt nearCenter31Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter31Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter31Lo : ℝ := (89908862188212943/62500000000000000)
def nearCenter31Hi : ℝ := (1438541795011407089/1000000000000000000)

theorem nearCenter31_bounds :
    nearCenter31Lo ≤ (constructionCenter 3).2 - T/2 ∧
    (constructionCenter 3).2 - T/2 ≤ nearCenter31Hi := by
  have hp := polynomial_interval nearCenter31Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter31Lo ≤
      polynomialLower nearCenter31Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter31Lo, polynomialLower, nearCenter31Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter31Coeffs nearRootLo nearRootHi ≤
      nearCenter31Hi := by
    norm_num [nearCenter31Hi, polynomialUpper, nearCenter31Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter31_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
