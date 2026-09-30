import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 0. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter00Coeffs : Fin 8 → ℚ := ![(-3/4), (-37/16), (5/2), (-35/16), -4, (-15/16), (15/4), (-25/16)]

theorem nearCenter00_poly :
    (constructionCenter 0).1 - T/2 = polynomialAt nearCenter00Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter00Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter00Lo : ℝ := (-1438541795011407089/1000000000000000000)
def nearCenter00Hi : ℝ := (-89908862188212943/62500000000000000)

theorem nearCenter00_bounds :
    nearCenter00Lo ≤ (constructionCenter 0).1 - T/2 ∧
    (constructionCenter 0).1 - T/2 ≤ nearCenter00Hi := by
  have hp := polynomial_interval nearCenter00Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter00Lo ≤
      polynomialLower nearCenter00Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter00Lo, polynomialLower, nearCenter00Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter00Coeffs nearRootLo nearRootHi ≤
      nearCenter00Hi := by
    norm_num [nearCenter00Hi, polynomialUpper, nearCenter00Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter00_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter01Coeffs : Fin 8 → ℚ := ![(-3/4), (-37/16), (5/2), (-35/16), -4, (-15/16), (15/4), (-25/16)]

theorem nearCenter01_poly :
    (constructionCenter 0).2 - T/2 = polynomialAt nearCenter01Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter01Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter01Lo : ℝ := (-1438541795011407089/1000000000000000000)
def nearCenter01Hi : ℝ := (-89908862188212943/62500000000000000)

theorem nearCenter01_bounds :
    nearCenter01Lo ≤ (constructionCenter 0).2 - T/2 ∧
    (constructionCenter 0).2 - T/2 ≤ nearCenter01Hi := by
  have hp := polynomial_interval nearCenter01Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter01Lo ≤
      polynomialLower nearCenter01Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter01Lo, polynomialLower, nearCenter01Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter01Coeffs nearRootLo nearRootHi ≤
      nearCenter01Hi := by
    norm_num [nearCenter01Hi, polynomialUpper, nearCenter01Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter01_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
