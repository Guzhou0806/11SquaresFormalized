import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 8. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter80Coeffs : Fin 8 → ℚ := ![(119/400), (-77/50), (629/400), (51/25), (-79/80), (-119/100), (15/16), (-3/20)]

theorem nearCenter80_poly :
    (constructionCenter 8).1 - T/2 = polynomialAt nearCenter80Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400)) - constructionSide/2 = polynomialAt nearCenter80Coeffs u
  simp [constructionSide, polynomialAt, nearCenter80Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter80Lo : ℝ := (21071032880374591/1000000000000000000)
def nearCenter80Hi : ℝ := (329234888755853/15625000000000000)

theorem nearCenter80_bounds :
    nearCenter80Lo ≤ (constructionCenter 8).1 - T/2 ∧
    (constructionCenter 8).1 - T/2 ≤ nearCenter80Hi := by
  have hp := polynomial_interval nearCenter80Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter80Lo ≤
      polynomialLower nearCenter80Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter80Lo, polynomialLower, nearCenter80Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter80Coeffs nearRootLo nearRootHi ≤
      nearCenter80Hi := by
    norm_num [nearCenter80Hi, polynomialUpper, nearCenter80Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter80_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter81Coeffs : Fin 8 → ℚ := ![(183/400), (-31/200), (-947/400), (481/200), (257/80), (-191/200), (-25/16), (33/40)]

theorem nearCenter81_poly :
    (constructionCenter 8).2 - T/2 = polynomialAt nearCenter81Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)) - constructionSide/2 = polynomialAt nearCenter81Coeffs u
  simp [constructionSide, polynomialAt, nearCenter81Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter81Lo : ℝ := (249983094684235383/1000000000000000000)
def nearCenter81Hi : ℝ := (31247886835529423/125000000000000000)

theorem nearCenter81_bounds :
    nearCenter81Lo ≤ (constructionCenter 8).2 - T/2 ∧
    (constructionCenter 8).2 - T/2 ≤ nearCenter81Hi := by
  have hp := polynomial_interval nearCenter81Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter81Lo ≤
      polynomialLower nearCenter81Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter81Lo, polynomialLower, nearCenter81Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter81Coeffs nearRootLo nearRootHi ≤
      nearCenter81Hi := by
    norm_num [nearCenter81Hi, polynomialUpper, nearCenter81Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter81_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
