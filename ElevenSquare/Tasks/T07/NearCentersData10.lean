import ElevenSquare.Tasks.T07.NearAlgebra


/-! Certified algebraic center intervals for near role 10. -/

namespace ElevenSquare.Tasks.T07

open ElevenSquare

noncomputable section

def nearCenter100Coeffs : Fin 8 → ℚ := ![(57/80), (7/5), (-113/80), (57/20), (55/16), (13/20), (-55/16), (3/2)]

theorem nearCenter100_poly :
    (constructionCenter 10).1 - T/2 = polynomialAt nearCenter100Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80)) - constructionSide/2 = polynomialAt nearCenter100Coeffs u
  simp [constructionSide, polynomialAt, nearCenter100Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter100Lo : ℝ := (1233933625149647587/1000000000000000000)
def nearCenter100Hi : ℝ := (308483406287411897/250000000000000000)

theorem nearCenter100_bounds :
    nearCenter100Lo ≤ (constructionCenter 10).1 - T/2 ∧
    (constructionCenter 10).1 - T/2 ≤ nearCenter100Hi := by
  have hp := polynomial_interval nearCenter100Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter100Lo ≤
      polynomialLower nearCenter100Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter100Lo, polynomialLower, nearCenter100Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter100Coeffs nearRootLo nearRootHi ≤
      nearCenter100Hi := by
    norm_num [nearCenter100Hi, polynomialUpper, nearCenter100Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter100_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

def nearCenter101Coeffs : Fin 8 → ℚ := ![(19/80), (7/40), (-111/80), (193/40), (61/16), (-93/40), (-25/16), (9/8)]

theorem nearCenter101_poly :
    (constructionCenter 10).2 - T/2 = polynomialAt nearCenter101Coeffs u := by
  rw [← constructionSide_eq_T]
  change ((43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) - constructionSide/2 = polynomialAt nearCenter101Coeffs u
  simp [constructionSide, polynomialAt, nearCenter101Coeffs, Fin.sum_univ_succ]
  ring

def nearCenter101Lo : ℝ := (40225461469939189/100000000000000000)
def nearCenter101Hi : ℝ := (402254614699391891/1000000000000000000)

theorem nearCenter101_bounds :
    nearCenter101Lo ≤ (constructionCenter 10).2 - T/2 ∧
    (constructionCenter 10).2 - T/2 ≤ nearCenter101Hi := by
  have hp := polynomial_interval nearCenter101Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : nearCenter101Lo ≤
      polynomialLower nearCenter101Coeffs nearRootLo nearRootHi := by
    norm_num [nearCenter101Lo, polynomialLower, nearCenter101Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  have hh : polynomialUpper nearCenter101Coeffs nearRootLo nearRootHi ≤
      nearCenter101Hi := by
    norm_num [nearCenter101Hi, polynomialUpper, nearCenter101Coeffs,
      nearRootLo, nearRootHi, Fin.sum_univ_succ]
  rw [nearCenter101_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end

end ElevenSquare.Tasks.T07
