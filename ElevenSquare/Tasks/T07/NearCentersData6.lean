import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 6. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter60Coeffs : Fin 8 → ℚ := ![(-139/400), (-77/200), (-549/400), (-73/200), (99/80), (103/200), (-15/16), (11/40)]

theorem nearCenter60_poly :
    (constructionCenter 6).1 - T/2 = polynomialAt nearCenter60Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400)) - constructionSide/2 = polynomialAt nearCenter60Coeffs u
  simp [constructionSide, polynomialAt, nearCenter60Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter60Lo : ℝ := (-666287898967407359/1000000000000000000)
def nearCenter60Hi : ℝ := (-333143949483703679/500000000000000000)

theorem nearCenter60_bounds :
    nearCenter60Lo ≤ (constructionCenter 6).1 - T/2 ∧
    (constructionCenter 6).1 - T/2 ≤ nearCenter60Hi := by
  have hp := polynomial_interval nearCenter60Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter60Lo ≤
      polynomialLower nearCenter60Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter60Lo, polynomialLower, nearCenter60Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter60Coeffs nearRootLo nearRootHi ≤
      nearCenter60Hi := by
    norm_num [nearCenter60Hi, polynomialUpper, nearCenter60Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter60_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter61Coeffs : Fin 8 → ℚ := ![(-173/400), (11/200), (157/400), (-411/200), (-147/80), (171/200), (15/16), (-23/40)]

theorem nearCenter61_poly :
    (constructionCenter 6).2 - T/2 = polynomialAt nearCenter61Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) - constructionSide/2 = polynomialAt nearCenter61Coeffs u
  simp [constructionSide, polynomialAt, nearCenter61Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter61Lo : ℝ := (-485983621047749149/1000000000000000000)
def nearCenter61Hi : ℝ := (-121495905261937287/250000000000000000)

theorem nearCenter61_bounds :
    nearCenter61Lo ≤ (constructionCenter 6).2 - T/2 ∧
    (constructionCenter 6).2 - T/2 ≤ nearCenter61Hi := by
  have hp := polynomial_interval nearCenter61Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter61Lo ≤
      polynomialLower nearCenter61Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter61Lo, polynomialLower, nearCenter61Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter61Coeffs nearRootLo nearRootHi ≤
      nearCenter61Hi := by
    norm_num [nearCenter61Hi, polynomialUpper, nearCenter61Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter61_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
