import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row37_alias0_zero : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 =
      ((1027 / 3200) + (29 / 160) * u + (-999 / 3200) * u^2 + (-191 / 800) * u^3 + (337 / 3200) * u^4 + (9 / 80) * u^5 + (-41 / 640) * u^6) * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (-1*((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*(constructionCos) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(constructionSin)) - 1/2) = ((1027 / 3200) + (29 / 160) * u + (-999 / 3200) * u^2 + (-191 / 800) * u^3 + (337 / 3200) * u^4 + (9 / 80) * u^5 + (-41 / 640) * u^6) * endpointPolynomial u
        dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row37_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 21 = polynomialGradient 37 21 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 21 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 21 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 21
    _ = (-1*(((((1 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 37 21 := rfl

theorem row37_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 22 = polynomialGradient 37 22 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 22 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 22 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 22
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((1 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 37 22 := rfl

theorem row37_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 23 = polynomialGradient 37 23 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 23 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 23 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 23
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*1)) + (1 / 2)*(-(((constructionCos)*1)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*1)) + (1 / 2)*((-(constructionSin)*1))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) - polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u = ((-17 / 640) + (-3 / 64) * u + (19 / 640) * u^2 + (3 / 80) * u^3 + (-7 / 640) * u^4 + (-1 / 64) * u^5 + (1 / 128) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 37 23 := rfl

theorem row37_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 27 = polynomialGradient 37 27 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 27 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 27 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 27
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(1))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(41 / 40), (-1 / 10), (-79 / 40), (7 / 20), (11 / 8), (-1 / 10), (-5 / 8), (1 / 4)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 37 27 := rfl

theorem row37_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 28 = polynomialGradient 37 28 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 28 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 28 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 28
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(1))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*0)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*0))))) := rfl
    _ = polyEval ![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)] u := by
      rw [polyEval_vec]
      push_cast
      dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 37 28 := rfl

theorem row37_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 29 = polynomialGradient 37 29 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 29 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 29 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 29
    _ = (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) := rfl
    _ = polyEval ![(19 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)] u := by
      apply sub_eq_zero.mp
      calc
        (-1*(((((0 + (1 / 2)*((-(constructionSin)*0)) + (1 / 2)*(-(((constructionCos)*0)))))-(0))*(constructionCos) + (((0 + (1 / 2)*(((constructionCos)*0)) + (1 / 2)*((-(constructionSin)*0))))-(0))*(constructionSin)) + ((((((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80)) + (1 / 2)*(constructionCos) + (1 / 2)*(-(constructionSin))))-((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400)))*((-(constructionSin)*1)) + (((((1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) + (1 / 2)*(constructionSin) + (1 / 2)*(constructionCos)))-((117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)))*(((constructionCos)*1))))) - polyEval ![(19 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)] u = ((389 / 3200) + (-3 / 10) * u + (167 / 3200) * u^2 + (203 / 800) * u^3 + (-81 / 3200) * u^4 + (-19 / 160) * u^5 + (33 / 640) * u^6) * endpointPolynomial u := by
          rw [polyEval_vec]
          push_cast
          dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
          ring
        _ = 0 := by rw [u_polynomial, mul_zero]
    _ = polynomialGradient 37 29 := rfl

theorem row37_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = polynomialGradient 37 0 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 0 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 0
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 0 := rfl

theorem row37_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 1 = polynomialGradient 37 1 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 1 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 1 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 1
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 1 := rfl

theorem row37_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 2 = polynomialGradient 37 2 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 2 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 2 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 2
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 2 := rfl

theorem row37_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 3 = polynomialGradient 37 3 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 3 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 3 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 3
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 3 := rfl

theorem row37_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 4 = polynomialGradient 37 4 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 4 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 4 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 4
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 4 := rfl

theorem row37_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 5 = polynomialGradient 37 5 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 5 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 5 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 5
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 5 := rfl

theorem row37_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 6 = polynomialGradient 37 6 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 6 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 6 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 6
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 6 := rfl

theorem row37_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 7 = polynomialGradient 37 7 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 7 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 7 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 7
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 7 := rfl

theorem row37_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 8 = polynomialGradient 37 8 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 8 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 8 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 8
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 8 := rfl

theorem row37_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 9 = polynomialGradient 37 9 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 9 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 9 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 9
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 9 := rfl

theorem row37_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 10 = polynomialGradient 37 10 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 10 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 10 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 10
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 10 := rfl

theorem row37_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 11 = polynomialGradient 37 11 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 11 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 11 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 11
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 11 := rfl

theorem row37_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 12 = polynomialGradient 37 12 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 12 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 12 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 12
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 12 := rfl

theorem row37_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 13 = polynomialGradient 37 13 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 13 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 13 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 13
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 13 := rfl

theorem row37_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 14 = polynomialGradient 37 14 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 14 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 14 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 14
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 14 := rfl

theorem row37_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 15 = polynomialGradient 37 15 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 15 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 15 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 15
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 15 := rfl

theorem row37_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 16 = polynomialGradient 37 16 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 16 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 16 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 16
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 16 := rfl

theorem row37_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 17 = polynomialGradient 37 17 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 17 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 17 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 17
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 17 := rfl

theorem row37_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 18 = polynomialGradient 37 18 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 18 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 18 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 18
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 18 := rfl

theorem row37_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 19 = polynomialGradient 37 19 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 19 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 19 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 19
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 19 := rfl

theorem row37_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 20 = polynomialGradient 37 20 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 20 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 20 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 20
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 20 := rfl

theorem row37_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 24 = polynomialGradient 37 24 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 24 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 24 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 24
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 24 := rfl

theorem row37_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 25 = polynomialGradient 37 25 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 25 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 25 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 25
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 25 := rfl

theorem row37_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 26 = polynomialGradient 37 26 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 26 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 26 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 26
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 26 := rfl

theorem row37_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 30 = polynomialGradient 37 30 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 30 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 30 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 30
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 30 := rfl

theorem row37_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 31 = polynomialGradient 37 31 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 31 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 31 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 31
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 31 := rfl

theorem row37_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 32 = polynomialGradient 37 32 := by
  calc
    gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 32 = pairGradientFormula constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 32 := gapGradient_pair T constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 32
    _ = 0 := pairGradientFormula_zero constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 37 32 := rfl

theorem row37_alias0_gradient : gapGradient T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) = polynomialGradient 37 := by
  funext j
  fin_cases j
  · exact row37_alias0_coordinate_00
  · exact row37_alias0_coordinate_01
  · exact row37_alias0_coordinate_02
  · exact row37_alias0_coordinate_03
  · exact row37_alias0_coordinate_04
  · exact row37_alias0_coordinate_05
  · exact row37_alias0_coordinate_06
  · exact row37_alias0_coordinate_07
  · exact row37_alias0_coordinate_08
  · exact row37_alias0_coordinate_09
  · exact row37_alias0_coordinate_10
  · exact row37_alias0_coordinate_11
  · exact row37_alias0_coordinate_12
  · exact row37_alias0_coordinate_13
  · exact row37_alias0_coordinate_14
  · exact row37_alias0_coordinate_15
  · exact row37_alias0_coordinate_16
  · exact row37_alias0_coordinate_17
  · exact row37_alias0_coordinate_18
  · exact row37_alias0_coordinate_19
  · exact row37_alias0_coordinate_20
  · exact row37_alias0_coordinate_21
  · exact row37_alias0_coordinate_22
  · exact row37_alias0_coordinate_23
  · exact row37_alias0_coordinate_24
  · exact row37_alias0_coordinate_25
  · exact row37_alias0_coordinate_26
  · exact row37_alias0_coordinate_27
  · exact row37_alias0_coordinate_28
  · exact row37_alias0_coordinate_29
  · exact row37_alias0_coordinate_30
  · exact row37_alias0_coordinate_31
  · exact row37_alias0_coordinate_32

theorem row37_aliases_tied (g : Gap) (hg : g ∈ rowAliases 37) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 37 := by
  change g ∈ [Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row37_alias0_zero, row37_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
