import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row45_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*(1) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(0)) - 1/2) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row45_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 12 = polynomialGradient 45 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 12 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 12 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 12
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(1))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 45 12 := rfl

theorem row45_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 13 = polynomialGradient 45 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 13 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 13 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 13
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(1))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 45 13 := rfl

theorem row45_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 14 = polynomialGradient 45 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 14 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 14 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 14
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*1)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*1))))) := rfl
    _ = polyEval ![(3 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 45 14 := rfl

theorem row45_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 15 = polynomialGradient 45 15 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 15 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 15 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 15
    _ = (-1*(((((1 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 45 15 := rfl

theorem row45_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 16 = polynomialGradient 45 16 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 16 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 16 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 16
    _ = (-1*(((((0 + (1 / 2)*((-(0)*0)) + (-1 / 2)*(-(((1)*0)))))-(0))*(1) + (((1 + (1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 45 16 := rfl

theorem row45_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 17 = polynomialGradient 45 17 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 17 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 17 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 17
    _ = (-1*(((((0 + (1 / 2)*((-(0)*1)) + (-1 / 2)*(-(((1)*1)))))-(0))*(1) + (((0 + (1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))))-(0))*(0)) + ((((((1 / 2)) + (1 / 2)*(1) + (-1 / 2)*(-(0))))-((3 / 2)))*((-(0)*0)) + (((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) + (1 / 2)*(0) + (-1 / 2)*(1)))-((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2))*(((1)*0))))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 45 17 := rfl

theorem row45_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = polynomialGradient 45 0 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 0 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 0
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 0 := rfl

theorem row45_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 1 = polynomialGradient 45 1 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 1 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 1 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 1
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 1 := rfl

theorem row45_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 2 = polynomialGradient 45 2 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 2 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 2 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 2
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 2 := rfl

theorem row45_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 3 = polynomialGradient 45 3 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 3 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 3 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 3
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 3 := rfl

theorem row45_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 4 = polynomialGradient 45 4 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 4 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 4 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 4
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 4 := rfl

theorem row45_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 5 = polynomialGradient 45 5 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 5 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 5 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 5
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 5 := rfl

theorem row45_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 6 = polynomialGradient 45 6 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 6 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 6 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 6
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 6 := rfl

theorem row45_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 7 = polynomialGradient 45 7 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 7 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 7 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 7
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 7 := rfl

theorem row45_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 8 = polynomialGradient 45 8 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 8 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 8 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 8
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 8 := rfl

theorem row45_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 9 = polynomialGradient 45 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 9 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 9 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 9
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 9 := rfl

theorem row45_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 10 = polynomialGradient 45 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 10 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 10 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 10
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 10 := rfl

theorem row45_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 11 = polynomialGradient 45 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 11 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 11 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 11
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 11 := rfl

theorem row45_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 18 = polynomialGradient 45 18 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 18 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 18 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 18
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 18 := rfl

theorem row45_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 19 = polynomialGradient 45 19 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 19 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 19 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 19
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 19 := rfl

theorem row45_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 20 = polynomialGradient 45 20 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 20 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 20 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 20
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 20 := rfl

theorem row45_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 21 = polynomialGradient 45 21 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 21 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 21 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 21
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 21 := rfl

theorem row45_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 22 = polynomialGradient 45 22 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 22 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 22 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 22
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 22 := rfl

theorem row45_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 23 = polynomialGradient 45 23 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 23 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 23 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 23
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 23 := rfl

theorem row45_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 24 = polynomialGradient 45 24 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 24 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 24 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 24
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 24 := rfl

theorem row45_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 25 = polynomialGradient 45 25 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 25 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 25 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 25
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 25 := rfl

theorem row45_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 26 = polynomialGradient 45 26 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 26 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 26 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 26
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 26 := rfl

theorem row45_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 27 = polynomialGradient 45 27 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 27 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 27 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 27
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 27 := rfl

theorem row45_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 28 = polynomialGradient 45 28 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 28 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 28 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 28
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 28 := rfl

theorem row45_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 29 = polynomialGradient 45 29 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 29 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 29 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 29
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 29 := rfl

theorem row45_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 30 = polynomialGradient 45 30 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 30 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 30 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 30
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 30 := rfl

theorem row45_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 31 = polynomialGradient 45 31 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 31 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 31 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 31
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 31 := rfl

theorem row45_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 32 = polynomialGradient 45 32 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) 32 = pairGradientFormula constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 32 := gapGradient_pair T constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 32
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 45 32 := rfl

theorem row45_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1) = polynomialGradient 45 := by
  funext j
  fin_cases j
  · exact row45_alias0_coordinate_00
  · exact row45_alias0_coordinate_01
  · exact row45_alias0_coordinate_02
  · exact row45_alias0_coordinate_03
  · exact row45_alias0_coordinate_04
  · exact row45_alias0_coordinate_05
  · exact row45_alias0_coordinate_06
  · exact row45_alias0_coordinate_07
  · exact row45_alias0_coordinate_08
  · exact row45_alias0_coordinate_09
  · exact row45_alias0_coordinate_10
  · exact row45_alias0_coordinate_11
  · exact row45_alias0_coordinate_12
  · exact row45_alias0_coordinate_13
  · exact row45_alias0_coordinate_14
  · exact row45_alias0_coordinate_15
  · exact row45_alias0_coordinate_16
  · exact row45_alias0_coordinate_17
  · exact row45_alias0_coordinate_18
  · exact row45_alias0_coordinate_19
  · exact row45_alias0_coordinate_20
  · exact row45_alias0_coordinate_21
  · exact row45_alias0_coordinate_22
  · exact row45_alias0_coordinate_23
  · exact row45_alias0_coordinate_24
  · exact row45_alias0_coordinate_25
  · exact row45_alias0_coordinate_26
  · exact row45_alias0_coordinate_27
  · exact row45_alias0_coordinate_28
  · exact row45_alias0_coordinate_29
  · exact row45_alias0_coordinate_30
  · exact row45_alias0_coordinate_31
  · exact row45_alias0_coordinate_32

theorem row45_aliases_tied (g : Gap) (hg : g ∈ rowAliases 45) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 45 := by
  change g ∈ [Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row45_alias0_zero, row45_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
