import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 2. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter20Coeffs : Fin 8 → ℚ := ![(3/4), (3/16), (-9/4), (5/16), (7/2), (9/16), (-5/2), (15/16)]

theorem nearCenter20_poly :
    (constructionCenter 2).1 - T/2 = polynomialAt nearCenter20Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter20Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter20Lo : ℝ := (297008259669103849/500000000000000000)
def nearCenter20Hi : ℝ := (594016519338207699/1000000000000000000)

theorem nearCenter20_bounds :
    nearCenter20Lo ≤ (constructionCenter 2).1 - T/2 ∧
    (constructionCenter 2).1 - T/2 ≤ nearCenter20Hi := by
  have hp := polynomial_interval nearCenter20Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter20Lo ≤
      polynomialLower nearCenter20Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter20Lo, polynomialLower, nearCenter20Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter20Coeffs nearRootLo nearRootHi ≤
      nearCenter20Hi := by
    norm_num [nearCenter20Hi, polynomialUpper, nearCenter20Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter20_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter21Coeffs : Fin 8 → ℚ := ![(3/4), (37/16), (-5/2), (35/16), 4, (15/16), (-15/4), (25/16)]

theorem nearCenter21_poly :
    (constructionCenter 2).2 - T/2 = polynomialAt nearCenter21Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, nearCenter21Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter21Lo : ℝ := (89908862188212943/62500000000000000)
def nearCenter21Hi : ℝ := (1438541795011407089/1000000000000000000)

theorem nearCenter21_bounds :
    nearCenter21Lo ≤ (constructionCenter 2).2 - T/2 ∧
    (constructionCenter 2).2 - T/2 ≤ nearCenter21Hi := by
  have hp := polynomial_interval nearCenter21Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter21Lo ≤
      polynomialLower nearCenter21Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter21Lo, polynomialLower, nearCenter21Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter21Coeffs nearRootLo nearRootHi ≤
      nearCenter21Hi := by
    norm_num [nearCenter21Hi, polynomialUpper, nearCenter21Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter21_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
