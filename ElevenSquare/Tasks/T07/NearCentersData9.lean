import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 9. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter90Coeffs : Fin 8 → ℚ := ![(153/400), (29/200), (-177/400), (1121/200), (207/80), (-231/200), (-35/16), (53/40)]

theorem nearCenter90_poly :
    (constructionCenter 9).1 - T/2 = polynomialAt nearCenter90Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)) - constructionSide/2 = polynomialAt nearCenter90Coeffs u
  simp [constructionSide, polynomialAt, nearCenter90Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter90Lo : ℝ := (685292030633915771/1000000000000000000)
def nearCenter90Hi : ℝ := (171323007658478943/250000000000000000)

theorem nearCenter90_bounds :
    nearCenter90Lo ≤ (constructionCenter 9).1 - T/2 ∧
    (constructionCenter 9).1 - T/2 ≤ nearCenter90Hi := by
  have hp := polynomial_interval nearCenter90Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter90Lo ≤
      polynomialLower nearCenter90Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter90Lo, polynomialLower, nearCenter90Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter90Coeffs nearRootLo nearRootHi ≤
      nearCenter90Hi := by
    norm_num [nearCenter90Hi, polynomialUpper, nearCenter90Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter90_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter91Coeffs : Fin 8 → ℚ := ![(71/400), (-161/100), (-539/400), (161/100), (129/80), (-123/50), (15/16), (-1/10)]

theorem nearCenter91_poly :
    (constructionCenter 9).2 - T/2 = polynomialAt nearCenter91Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) - constructionSide/2 = polynomialAt nearCenter91Coeffs u
  simp [constructionSide, polynomialAt, nearCenter91Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter91Lo : ℝ := (-31122931838603941/62500000000000000)
def nearCenter91Hi : ℝ := (-99593381883532611/200000000000000000)

theorem nearCenter91_bounds :
    nearCenter91Lo ≤ (constructionCenter 9).2 - T/2 ∧
    (constructionCenter 9).2 - T/2 ≤ nearCenter91Hi := by
  have hp := polynomial_interval nearCenter91Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter91Lo ≤
      polynomialLower nearCenter91Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter91Lo, polynomialLower, nearCenter91Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter91Coeffs nearRootLo nearRootHi ≤
      nearCenter91Hi := by
    norm_num [nearCenter91Hi, polynomialUpper, nearCenter91Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter91_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
