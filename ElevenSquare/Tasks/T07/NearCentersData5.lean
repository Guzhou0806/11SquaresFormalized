import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 5. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter50Coeffs : Fin 8 → ℚ := ![(-3/4), (-37/16), (5/2), (-35/16), -4, (-15/16), (15/4), (-25/16)]

theorem nearCenter50_poly :
    (constructionCenter 5).1 - T/2 = polynomialAt nearCenter50Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((1 / 2)) - constructionSide/2 = polynomialAt nearCenter50Coeffs u
  simp [constructionSide, polynomialAt, nearCenter50Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter50Lo : ℝ := (-1438541795011407089/1000000000000000000)
def nearCenter50Hi : ℝ := (-89908862188212943/62500000000000000)

theorem nearCenter50_bounds :
    nearCenter50Lo ≤ (constructionCenter 5).1 - T/2 ∧
    (constructionCenter 5).1 - T/2 ≤ nearCenter50Hi := by
  have hp := polynomial_interval nearCenter50Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter50Lo ≤
      polynomialLower nearCenter50Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter50Lo, polynomialLower, nearCenter50Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter50Coeffs nearRootLo nearRootHi ≤
      nearCenter50Hi := by
    norm_num [nearCenter50Hi, polynomialUpper, nearCenter50Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter50_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter51Coeffs : Fin 8 → ℚ := ![(-1/4), (37/16), (-5/2), (35/16), 4, (15/16), (-15/4), (25/16)]

theorem nearCenter51_poly :
    (constructionCenter 5).2 - T/2 = polynomialAt nearCenter51Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) - constructionSide/2 = polynomialAt nearCenter51Coeffs u
  simp [constructionSide, polynomialAt, nearCenter51Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter51Lo : ℝ := (27408862188212943/62500000000000000)
def nearCenter51Hi : ℝ := (438541795011407089/1000000000000000000)

theorem nearCenter51_bounds :
    nearCenter51Lo ≤ (constructionCenter 5).2 - T/2 ∧
    (constructionCenter 5).2 - T/2 ≤ nearCenter51Hi := by
  have hp := polynomial_interval nearCenter51Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter51Lo ≤
      polynomialLower nearCenter51Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter51Lo, polynomialLower, nearCenter51Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter51Coeffs nearRootLo nearRootHi ≤
      nearCenter51Hi := by
    norm_num [nearCenter51Hi, polynomialUpper, nearCenter51Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter51_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
