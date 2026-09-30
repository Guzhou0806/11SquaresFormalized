import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row02_alias0_zero : gapValue T constructionSquare (Gap.wall 0 0 2) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 0 0 2) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (((1 / 2)) + (-1 / 2)*(0) + (-1 / 2)*(1)) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row02_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 0 0 2) 0 = polynomialGradient 2 0 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 0 = wallGradientFormula constructionSquare 0 0 2 0 := gapGradient_wall T constructionSquare 0 0 2 0
    _ = (0 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 2 0 := rfl

theorem row02_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 0 0 2) 1 = polynomialGradient 2 1 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 1 = wallGradientFormula constructionSquare 0 0 2 1 := gapGradient_wall T constructionSquare 0 0 2 1
    _ = (1 + (-1 / 2)*(((1)*0)) + (-1 / 2)*((-(0)*0))) := rfl
    _ = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 2 1 := rfl

theorem row02_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 0 0 2) 2 = polynomialGradient 2 2 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 2 = wallGradientFormula constructionSquare 0 0 2 2 := gapGradient_wall T constructionSquare 0 0 2 2
    _ = (0 + (-1 / 2)*(((1)*1)) + (-1 / 2)*((-(0)*1))) := rfl
    _ = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 2 2 := rfl

theorem row02_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 0 0 2) 3 = polynomialGradient 2 3 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 3 = wallGradientFormula constructionSquare 0 0 2 3 := gapGradient_wall T constructionSquare 0 0 2 3
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 3 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 3 := rfl

theorem row02_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 0 0 2) 4 = polynomialGradient 2 4 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 4 = wallGradientFormula constructionSquare 0 0 2 4 := gapGradient_wall T constructionSquare 0 0 2 4
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 4 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 4 := rfl

theorem row02_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 0 0 2) 5 = polynomialGradient 2 5 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 5 = wallGradientFormula constructionSquare 0 0 2 5 := gapGradient_wall T constructionSquare 0 0 2 5
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 5 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 5 := rfl

theorem row02_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 0 0 2) 6 = polynomialGradient 2 6 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 6 = wallGradientFormula constructionSquare 0 0 2 6 := gapGradient_wall T constructionSquare 0 0 2 6
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 6 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 6 := rfl

theorem row02_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 0 0 2) 7 = polynomialGradient 2 7 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 7 = wallGradientFormula constructionSquare 0 0 2 7 := gapGradient_wall T constructionSquare 0 0 2 7
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 7 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 7 := rfl

theorem row02_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 0 0 2) 8 = polynomialGradient 2 8 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 8 = wallGradientFormula constructionSquare 0 0 2 8 := gapGradient_wall T constructionSquare 0 0 2 8
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 8 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 8 := rfl

theorem row02_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 0 0 2) 9 = polynomialGradient 2 9 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 9 = wallGradientFormula constructionSquare 0 0 2 9 := gapGradient_wall T constructionSquare 0 0 2 9
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 9 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 9 := rfl

theorem row02_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 0 0 2) 10 = polynomialGradient 2 10 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 10 = wallGradientFormula constructionSquare 0 0 2 10 := gapGradient_wall T constructionSquare 0 0 2 10
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 10 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 10 := rfl

theorem row02_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 0 0 2) 11 = polynomialGradient 2 11 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 11 = wallGradientFormula constructionSquare 0 0 2 11 := gapGradient_wall T constructionSquare 0 0 2 11
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 11 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 11 := rfl

theorem row02_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 0 0 2) 12 = polynomialGradient 2 12 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 12 = wallGradientFormula constructionSquare 0 0 2 12 := gapGradient_wall T constructionSquare 0 0 2 12
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 12 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 12 := rfl

theorem row02_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 0 0 2) 13 = polynomialGradient 2 13 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 13 = wallGradientFormula constructionSquare 0 0 2 13 := gapGradient_wall T constructionSquare 0 0 2 13
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 13 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 13 := rfl

theorem row02_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 0 0 2) 14 = polynomialGradient 2 14 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 14 = wallGradientFormula constructionSquare 0 0 2 14 := gapGradient_wall T constructionSquare 0 0 2 14
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 14 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 14 := rfl

theorem row02_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 0 0 2) 15 = polynomialGradient 2 15 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 15 = wallGradientFormula constructionSquare 0 0 2 15 := gapGradient_wall T constructionSquare 0 0 2 15
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 15 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 15 := rfl

theorem row02_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 0 0 2) 16 = polynomialGradient 2 16 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 16 = wallGradientFormula constructionSquare 0 0 2 16 := gapGradient_wall T constructionSquare 0 0 2 16
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 16 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 16 := rfl

theorem row02_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 0 0 2) 17 = polynomialGradient 2 17 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 17 = wallGradientFormula constructionSquare 0 0 2 17 := gapGradient_wall T constructionSquare 0 0 2 17
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 17 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 17 := rfl

theorem row02_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 0 0 2) 18 = polynomialGradient 2 18 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 18 = wallGradientFormula constructionSquare 0 0 2 18 := gapGradient_wall T constructionSquare 0 0 2 18
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 18 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 18 := rfl

theorem row02_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 0 0 2) 19 = polynomialGradient 2 19 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 19 = wallGradientFormula constructionSquare 0 0 2 19 := gapGradient_wall T constructionSquare 0 0 2 19
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 19 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 19 := rfl

theorem row02_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 0 0 2) 20 = polynomialGradient 2 20 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 20 = wallGradientFormula constructionSquare 0 0 2 20 := gapGradient_wall T constructionSquare 0 0 2 20
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 20 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 20 := rfl

theorem row02_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 0 0 2) 21 = polynomialGradient 2 21 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 21 = wallGradientFormula constructionSquare 0 0 2 21 := gapGradient_wall T constructionSquare 0 0 2 21
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 21 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 21 := rfl

theorem row02_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 0 0 2) 22 = polynomialGradient 2 22 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 22 = wallGradientFormula constructionSquare 0 0 2 22 := gapGradient_wall T constructionSquare 0 0 2 22
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 22 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 22 := rfl

theorem row02_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 0 0 2) 23 = polynomialGradient 2 23 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 23 = wallGradientFormula constructionSquare 0 0 2 23 := gapGradient_wall T constructionSquare 0 0 2 23
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 23 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 23 := rfl

theorem row02_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 0 0 2) 24 = polynomialGradient 2 24 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 24 = wallGradientFormula constructionSquare 0 0 2 24 := gapGradient_wall T constructionSquare 0 0 2 24
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 24 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 24 := rfl

theorem row02_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 0 0 2) 25 = polynomialGradient 2 25 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 25 = wallGradientFormula constructionSquare 0 0 2 25 := gapGradient_wall T constructionSquare 0 0 2 25
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 25 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 25 := rfl

theorem row02_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 0 0 2) 26 = polynomialGradient 2 26 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 26 = wallGradientFormula constructionSquare 0 0 2 26 := gapGradient_wall T constructionSquare 0 0 2 26
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 26 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 26 := rfl

theorem row02_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 0 0 2) 27 = polynomialGradient 2 27 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 27 = wallGradientFormula constructionSquare 0 0 2 27 := gapGradient_wall T constructionSquare 0 0 2 27
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 27 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 27 := rfl

theorem row02_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 0 0 2) 28 = polynomialGradient 2 28 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 28 = wallGradientFormula constructionSquare 0 0 2 28 := gapGradient_wall T constructionSquare 0 0 2 28
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 28 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 28 := rfl

theorem row02_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 0 0 2) 29 = polynomialGradient 2 29 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 29 = wallGradientFormula constructionSquare 0 0 2 29 := gapGradient_wall T constructionSquare 0 0 2 29
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 29 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 29 := rfl

theorem row02_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 0 0 2) 30 = polynomialGradient 2 30 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 30 = wallGradientFormula constructionSquare 0 0 2 30 := gapGradient_wall T constructionSquare 0 0 2 30
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 30 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 30 := rfl

theorem row02_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 0 0 2) 31 = polynomialGradient 2 31 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 31 = wallGradientFormula constructionSquare 0 0 2 31 := gapGradient_wall T constructionSquare 0 0 2 31
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 31 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 31 := rfl

theorem row02_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 0 0 2) 32 = polynomialGradient 2 32 := by
  calc
    gapGradient T constructionSquare (Gap.wall 0 0 2) 32 = wallGradientFormula constructionSquare 0 0 2 32 := gapGradient_wall T constructionSquare 0 0 2 32
    _ = 0 := wallGradientFormula_zero constructionSquare 0 0 2 32 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 2 32 := rfl

theorem row02_alias0_gradient : gapGradient T constructionSquare (Gap.wall 0 0 2) = polynomialGradient 2 := by
  funext j
  fin_cases j
  · exact row02_alias0_coordinate_00
  · exact row02_alias0_coordinate_01
  · exact row02_alias0_coordinate_02
  · exact row02_alias0_coordinate_03
  · exact row02_alias0_coordinate_04
  · exact row02_alias0_coordinate_05
  · exact row02_alias0_coordinate_06
  · exact row02_alias0_coordinate_07
  · exact row02_alias0_coordinate_08
  · exact row02_alias0_coordinate_09
  · exact row02_alias0_coordinate_10
  · exact row02_alias0_coordinate_11
  · exact row02_alias0_coordinate_12
  · exact row02_alias0_coordinate_13
  · exact row02_alias0_coordinate_14
  · exact row02_alias0_coordinate_15
  · exact row02_alias0_coordinate_16
  · exact row02_alias0_coordinate_17
  · exact row02_alias0_coordinate_18
  · exact row02_alias0_coordinate_19
  · exact row02_alias0_coordinate_20
  · exact row02_alias0_coordinate_21
  · exact row02_alias0_coordinate_22
  · exact row02_alias0_coordinate_23
  · exact row02_alias0_coordinate_24
  · exact row02_alias0_coordinate_25
  · exact row02_alias0_coordinate_26
  · exact row02_alias0_coordinate_27
  · exact row02_alias0_coordinate_28
  · exact row02_alias0_coordinate_29
  · exact row02_alias0_coordinate_30
  · exact row02_alias0_coordinate_31
  · exact row02_alias0_coordinate_32

theorem row02_aliases_tied (g : Gap) (hg : g ∈ rowAliases 2) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 2 := by
  change g ∈ [Gap.wall 0 0 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row02_alias0_zero, row02_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
