import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 7. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter70Coeffs : Fin 8 → ℚ := ![(-21/80), (13/10), (-271/80), (16/5), (77/16), (11/20), (-65/16), (7/4)]

theorem nearCenter70_poly :
    (constructionCenter 7).1 - T/2 = polynomialAt nearCenter70Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) - constructionSide/2 = polynomialAt nearCenter70Coeffs u
  simp [constructionSide, polynomialAt, nearCenter70Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter70Lo : ℝ := (-1033450606933089/500000000000000000)
def nearCenter70Hi : ℝ := (-2066901213866177/1000000000000000000)

theorem nearCenter70_bounds :
    nearCenter70Lo ≤ (constructionCenter 7).1 - T/2 ∧
    (constructionCenter 7).1 - T/2 ≤ nearCenter70Hi := by
  have hp := polynomial_interval nearCenter70Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter70Lo ≤
      polynomialLower nearCenter70Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter70Lo, polynomialLower, nearCenter70Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter70Coeffs nearRootLo nearRootHi ≤
      nearCenter70Hi := by
    norm_num [nearCenter70Hi, polynomialUpper, nearCenter70Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter70_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter71Coeffs : Fin 8 → ℚ := ![(-57/80), (-7/5), (113/80), (-57/20), (-55/16), (-13/20), (55/16), (-3/2)]

theorem nearCenter71_poly :
    (constructionCenter 7).2 - T/2 = polynomialAt nearCenter71Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) - constructionSide/2 = polynomialAt nearCenter71Coeffs u
  simp [constructionSide, polynomialAt, nearCenter71Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter71Lo : ℝ := (-308483406287411897/250000000000000000)
def nearCenter71Hi : ℝ := (-1233933625149647587/1000000000000000000)

theorem nearCenter71_bounds :
    nearCenter71Lo ≤ (constructionCenter 7).2 - T/2 ∧
    (constructionCenter 7).2 - T/2 ≤ nearCenter71Hi := by
  have hp := polynomial_interval nearCenter71Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter71Lo ≤
      polynomialLower nearCenter71Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter71Lo, polynomialLower, nearCenter71Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter71Coeffs nearRootLo nearRootHi ≤
      nearCenter71Hi := by
    norm_num [nearCenter71Hi, polynomialUpper, nearCenter71Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter71_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
