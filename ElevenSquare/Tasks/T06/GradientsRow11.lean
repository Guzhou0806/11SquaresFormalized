import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row11_alias0_zero : gapValue T constructionSquare (Gap.wall 3 3 0) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 3 3 0) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (((1 / 2)) + (-1 / 2)*(1) + (1 / 2)*(-(0))) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row11_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 3 3 0) 9 = polynomialGradient 11 9 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 9 = wallGradientFormula constructionSquare 3 3 0 9 := gapGradient_wall T constructionSquare 3 3 0 9
    _ = (1 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 11 9 := rfl

theorem row11_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 3 3 0) 10 = polynomialGradient 11 10 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 10 = wallGradientFormula constructionSquare 3 3 0 10 := gapGradient_wall T constructionSquare 3 3 0 10
    _ = (0 + (-1 / 2)*((-(0)*0)) + (1 / 2)*(-(((1)*0)))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 11 10 := rfl

theorem row11_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 3 3 0) 11 = polynomialGradient 11 11 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 11 = wallGradientFormula constructionSquare 3 3 0 11 := gapGradient_wall T constructionSquare 3 3 0 11
    _ = (0 + (-1 / 2)*((-(0)*1)) + (1 / 2)*(-(((1)*1)))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 11 11 := rfl

theorem row11_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 3 3 0) 0 = polynomialGradient 11 0 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 0 = wallGradientFormula constructionSquare 3 3 0 0 := gapGradient_wall T constructionSquare 3 3 0 0
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 0 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 0 := rfl

theorem row11_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 3 3 0) 1 = polynomialGradient 11 1 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 1 = wallGradientFormula constructionSquare 3 3 0 1 := gapGradient_wall T constructionSquare 3 3 0 1
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 1 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 1 := rfl

theorem row11_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 3 3 0) 2 = polynomialGradient 11 2 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 2 = wallGradientFormula constructionSquare 3 3 0 2 := gapGradient_wall T constructionSquare 3 3 0 2
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 2 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 2 := rfl

theorem row11_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 3 3 0) 3 = polynomialGradient 11 3 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 3 = wallGradientFormula constructionSquare 3 3 0 3 := gapGradient_wall T constructionSquare 3 3 0 3
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 3 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 3 := rfl

theorem row11_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 3 3 0) 4 = polynomialGradient 11 4 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 4 = wallGradientFormula constructionSquare 3 3 0 4 := gapGradient_wall T constructionSquare 3 3 0 4
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 4 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 4 := rfl

theorem row11_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 3 3 0) 5 = polynomialGradient 11 5 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 5 = wallGradientFormula constructionSquare 3 3 0 5 := gapGradient_wall T constructionSquare 3 3 0 5
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 5 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 5 := rfl

theorem row11_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 3 3 0) 6 = polynomialGradient 11 6 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 6 = wallGradientFormula constructionSquare 3 3 0 6 := gapGradient_wall T constructionSquare 3 3 0 6
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 6 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 6 := rfl

theorem row11_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 3 3 0) 7 = polynomialGradient 11 7 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 7 = wallGradientFormula constructionSquare 3 3 0 7 := gapGradient_wall T constructionSquare 3 3 0 7
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 7 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 7 := rfl

theorem row11_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 3 3 0) 8 = polynomialGradient 11 8 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 8 = wallGradientFormula constructionSquare 3 3 0 8 := gapGradient_wall T constructionSquare 3 3 0 8
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 8 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 8 := rfl

theorem row11_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 3 3 0) 12 = polynomialGradient 11 12 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 12 = wallGradientFormula constructionSquare 3 3 0 12 := gapGradient_wall T constructionSquare 3 3 0 12
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 12 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 12 := rfl

theorem row11_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 3 3 0) 13 = polynomialGradient 11 13 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 13 = wallGradientFormula constructionSquare 3 3 0 13 := gapGradient_wall T constructionSquare 3 3 0 13
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 13 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 13 := rfl

theorem row11_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 3 3 0) 14 = polynomialGradient 11 14 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 14 = wallGradientFormula constructionSquare 3 3 0 14 := gapGradient_wall T constructionSquare 3 3 0 14
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 14 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 14 := rfl

theorem row11_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 3 3 0) 15 = polynomialGradient 11 15 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 15 = wallGradientFormula constructionSquare 3 3 0 15 := gapGradient_wall T constructionSquare 3 3 0 15
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 15 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 15 := rfl

theorem row11_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 3 3 0) 16 = polynomialGradient 11 16 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 16 = wallGradientFormula constructionSquare 3 3 0 16 := gapGradient_wall T constructionSquare 3 3 0 16
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 16 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 16 := rfl

theorem row11_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 3 3 0) 17 = polynomialGradient 11 17 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 17 = wallGradientFormula constructionSquare 3 3 0 17 := gapGradient_wall T constructionSquare 3 3 0 17
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 17 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 17 := rfl

theorem row11_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 3 3 0) 18 = polynomialGradient 11 18 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 18 = wallGradientFormula constructionSquare 3 3 0 18 := gapGradient_wall T constructionSquare 3 3 0 18
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 18 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 18 := rfl

theorem row11_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 3 3 0) 19 = polynomialGradient 11 19 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 19 = wallGradientFormula constructionSquare 3 3 0 19 := gapGradient_wall T constructionSquare 3 3 0 19
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 19 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 19 := rfl

theorem row11_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 3 3 0) 20 = polynomialGradient 11 20 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 20 = wallGradientFormula constructionSquare 3 3 0 20 := gapGradient_wall T constructionSquare 3 3 0 20
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 20 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 20 := rfl

theorem row11_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 3 3 0) 21 = polynomialGradient 11 21 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 21 = wallGradientFormula constructionSquare 3 3 0 21 := gapGradient_wall T constructionSquare 3 3 0 21
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 21 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 21 := rfl

theorem row11_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 3 3 0) 22 = polynomialGradient 11 22 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 22 = wallGradientFormula constructionSquare 3 3 0 22 := gapGradient_wall T constructionSquare 3 3 0 22
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 22 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 22 := rfl

theorem row11_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 3 3 0) 23 = polynomialGradient 11 23 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 23 = wallGradientFormula constructionSquare 3 3 0 23 := gapGradient_wall T constructionSquare 3 3 0 23
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 23 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 23 := rfl

theorem row11_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 3 3 0) 24 = polynomialGradient 11 24 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 24 = wallGradientFormula constructionSquare 3 3 0 24 := gapGradient_wall T constructionSquare 3 3 0 24
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 24 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 24 := rfl

theorem row11_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 3 3 0) 25 = polynomialGradient 11 25 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 25 = wallGradientFormula constructionSquare 3 3 0 25 := gapGradient_wall T constructionSquare 3 3 0 25
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 25 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 25 := rfl

theorem row11_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 3 3 0) 26 = polynomialGradient 11 26 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 26 = wallGradientFormula constructionSquare 3 3 0 26 := gapGradient_wall T constructionSquare 3 3 0 26
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 26 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 26 := rfl

theorem row11_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 3 3 0) 27 = polynomialGradient 11 27 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 27 = wallGradientFormula constructionSquare 3 3 0 27 := gapGradient_wall T constructionSquare 3 3 0 27
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 27 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 27 := rfl

theorem row11_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 3 3 0) 28 = polynomialGradient 11 28 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 28 = wallGradientFormula constructionSquare 3 3 0 28 := gapGradient_wall T constructionSquare 3 3 0 28
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 28 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 28 := rfl

theorem row11_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 3 3 0) 29 = polynomialGradient 11 29 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 29 = wallGradientFormula constructionSquare 3 3 0 29 := gapGradient_wall T constructionSquare 3 3 0 29
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 29 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 29 := rfl

theorem row11_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 3 3 0) 30 = polynomialGradient 11 30 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 30 = wallGradientFormula constructionSquare 3 3 0 30 := gapGradient_wall T constructionSquare 3 3 0 30
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 30 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 30 := rfl

theorem row11_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 3 3 0) 31 = polynomialGradient 11 31 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 31 = wallGradientFormula constructionSquare 3 3 0 31 := gapGradient_wall T constructionSquare 3 3 0 31
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 31 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 31 := rfl

theorem row11_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 3 3 0) 32 = polynomialGradient 11 32 := by
  calc
    gapGradient T constructionSquare (Gap.wall 3 3 0) 32 = wallGradientFormula constructionSquare 3 3 0 32 := gapGradient_wall T constructionSquare 3 3 0 32
    _ = 0 := wallGradientFormula_zero constructionSquare 3 3 0 32 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 11 32 := rfl

theorem row11_alias0_gradient : gapGradient T constructionSquare (Gap.wall 3 3 0) = polynomialGradient 11 := by
  funext j
  fin_cases j
  · exact row11_alias0_coordinate_00
  · exact row11_alias0_coordinate_01
  · exact row11_alias0_coordinate_02
  · exact row11_alias0_coordinate_03
  · exact row11_alias0_coordinate_04
  · exact row11_alias0_coordinate_05
  · exact row11_alias0_coordinate_06
  · exact row11_alias0_coordinate_07
  · exact row11_alias0_coordinate_08
  · exact row11_alias0_coordinate_09
  · exact row11_alias0_coordinate_10
  · exact row11_alias0_coordinate_11
  · exact row11_alias0_coordinate_12
  · exact row11_alias0_coordinate_13
  · exact row11_alias0_coordinate_14
  · exact row11_alias0_coordinate_15
  · exact row11_alias0_coordinate_16
  · exact row11_alias0_coordinate_17
  · exact row11_alias0_coordinate_18
  · exact row11_alias0_coordinate_19
  · exact row11_alias0_coordinate_20
  · exact row11_alias0_coordinate_21
  · exact row11_alias0_coordinate_22
  · exact row11_alias0_coordinate_23
  · exact row11_alias0_coordinate_24
  · exact row11_alias0_coordinate_25
  · exact row11_alias0_coordinate_26
  · exact row11_alias0_coordinate_27
  · exact row11_alias0_coordinate_28
  · exact row11_alias0_coordinate_29
  · exact row11_alias0_coordinate_30
  · exact row11_alias0_coordinate_31
  · exact row11_alias0_coordinate_32

theorem row11_aliases_tied (g : Gap) (hg : g ∈ rowAliases 11) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 11 := by
  change g ∈ [Gap.wall 3 3 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row11_alias0_zero, row11_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
