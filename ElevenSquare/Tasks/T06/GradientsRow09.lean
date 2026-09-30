import ElevenSquare.Tasks.T06.GradientsFinValues
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsSupport

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row09_alias0_zero : gapValue T constructionSquare (Gap.wall 2 3 3) 0 = 0 := by
  rw [← constructionSide_eq_T]
  calc
    gapValue constructionSide constructionSquare (Gap.wall 2 3 3) 0 =
      0 * endpointPolynomial u := by
        simp only [gapValue, featureGap, perturbedCorner_zero, perturbedCenter_zero, perturbedAxis_zero]
        change (constructionSide-((((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) + (-1 / 2)*(0) + (1 / 2)*(1)))) = 0 * endpointPolynomial u
        try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
        ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem row09_alias0_coordinate_06 : gapGradient T constructionSquare (Gap.wall 2 3 3) 6 = polynomialGradient 9 6 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 6 = wallGradientFormula constructionSquare 2 3 3 6 := gapGradient_wall T constructionSquare 2 3 3 6
    _ = (-((0 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))) := rfl
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 9 6 := rfl

theorem row09_alias0_coordinate_07 : gapGradient T constructionSquare (Gap.wall 2 3 3) 7 = polynomialGradient 9 7 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 7 = wallGradientFormula constructionSquare 2 3 3 7 := gapGradient_wall T constructionSquare 2 3 3 7
    _ = (-((1 + (-1 / 2)*(((1)*0)) + (1 / 2)*((-(0)*0))))) := rfl
    _ = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 9 7 := rfl

theorem row09_alias0_coordinate_08 : gapGradient T constructionSquare (Gap.wall 2 3 3) 8 = polynomialGradient 9 8 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 8 = wallGradientFormula constructionSquare 2 3 3 8 := gapGradient_wall T constructionSquare 2 3 3 8
    _ = (-((0 + (-1 / 2)*(((1)*1)) + (1 / 2)*((-(0)*1))))) := rfl
    _ = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
      rw [polyEval_vec]
      push_cast
      try dsimp only [constructionCos, constructionSin, constructionSide, endpointPolynomial]
      ring
    _ = polynomialGradient 9 8 := rfl

theorem row09_alias0_coordinate_00 : gapGradient T constructionSquare (Gap.wall 2 3 3) 0 = polynomialGradient 9 0 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 0 = wallGradientFormula constructionSquare 2 3 3 0 := gapGradient_wall T constructionSquare 2 3 3 0
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 0 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 0 := rfl

theorem row09_alias0_coordinate_01 : gapGradient T constructionSquare (Gap.wall 2 3 3) 1 = polynomialGradient 9 1 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 1 = wallGradientFormula constructionSquare 2 3 3 1 := gapGradient_wall T constructionSquare 2 3 3 1
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 1 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 1 := rfl

theorem row09_alias0_coordinate_02 : gapGradient T constructionSquare (Gap.wall 2 3 3) 2 = polynomialGradient 9 2 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 2 = wallGradientFormula constructionSquare 2 3 3 2 := gapGradient_wall T constructionSquare 2 3 3 2
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 2 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 2 := rfl

theorem row09_alias0_coordinate_03 : gapGradient T constructionSquare (Gap.wall 2 3 3) 3 = polynomialGradient 9 3 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 3 = wallGradientFormula constructionSquare 2 3 3 3 := gapGradient_wall T constructionSquare 2 3 3 3
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 3 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 3 := rfl

theorem row09_alias0_coordinate_04 : gapGradient T constructionSquare (Gap.wall 2 3 3) 4 = polynomialGradient 9 4 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 4 = wallGradientFormula constructionSquare 2 3 3 4 := gapGradient_wall T constructionSquare 2 3 3 4
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 4 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 4 := rfl

theorem row09_alias0_coordinate_05 : gapGradient T constructionSquare (Gap.wall 2 3 3) 5 = polynomialGradient 9 5 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 5 = wallGradientFormula constructionSquare 2 3 3 5 := gapGradient_wall T constructionSquare 2 3 3 5
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 5 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 5 := rfl

theorem row09_alias0_coordinate_09 : gapGradient T constructionSquare (Gap.wall 2 3 3) 9 = polynomialGradient 9 9 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 9 = wallGradientFormula constructionSquare 2 3 3 9 := gapGradient_wall T constructionSquare 2 3 3 9
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 9 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 9 := rfl

theorem row09_alias0_coordinate_10 : gapGradient T constructionSquare (Gap.wall 2 3 3) 10 = polynomialGradient 9 10 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 10 = wallGradientFormula constructionSquare 2 3 3 10 := gapGradient_wall T constructionSquare 2 3 3 10
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 10 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 10 := rfl

theorem row09_alias0_coordinate_11 : gapGradient T constructionSquare (Gap.wall 2 3 3) 11 = polynomialGradient 9 11 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 11 = wallGradientFormula constructionSquare 2 3 3 11 := gapGradient_wall T constructionSquare 2 3 3 11
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 11 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 11 := rfl

theorem row09_alias0_coordinate_12 : gapGradient T constructionSquare (Gap.wall 2 3 3) 12 = polynomialGradient 9 12 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 12 = wallGradientFormula constructionSquare 2 3 3 12 := gapGradient_wall T constructionSquare 2 3 3 12
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 12 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 12 := rfl

theorem row09_alias0_coordinate_13 : gapGradient T constructionSquare (Gap.wall 2 3 3) 13 = polynomialGradient 9 13 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 13 = wallGradientFormula constructionSquare 2 3 3 13 := gapGradient_wall T constructionSquare 2 3 3 13
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 13 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 13 := rfl

theorem row09_alias0_coordinate_14 : gapGradient T constructionSquare (Gap.wall 2 3 3) 14 = polynomialGradient 9 14 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 14 = wallGradientFormula constructionSquare 2 3 3 14 := gapGradient_wall T constructionSquare 2 3 3 14
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 14 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 14 := rfl

theorem row09_alias0_coordinate_15 : gapGradient T constructionSquare (Gap.wall 2 3 3) 15 = polynomialGradient 9 15 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 15 = wallGradientFormula constructionSquare 2 3 3 15 := gapGradient_wall T constructionSquare 2 3 3 15
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 15 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 15 := rfl

theorem row09_alias0_coordinate_16 : gapGradient T constructionSquare (Gap.wall 2 3 3) 16 = polynomialGradient 9 16 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 16 = wallGradientFormula constructionSquare 2 3 3 16 := gapGradient_wall T constructionSquare 2 3 3 16
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 16 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 16 := rfl

theorem row09_alias0_coordinate_17 : gapGradient T constructionSquare (Gap.wall 2 3 3) 17 = polynomialGradient 9 17 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 17 = wallGradientFormula constructionSquare 2 3 3 17 := gapGradient_wall T constructionSquare 2 3 3 17
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 17 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 17 := rfl

theorem row09_alias0_coordinate_18 : gapGradient T constructionSquare (Gap.wall 2 3 3) 18 = polynomialGradient 9 18 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 18 = wallGradientFormula constructionSquare 2 3 3 18 := gapGradient_wall T constructionSquare 2 3 3 18
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 18 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 18 := rfl

theorem row09_alias0_coordinate_19 : gapGradient T constructionSquare (Gap.wall 2 3 3) 19 = polynomialGradient 9 19 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 19 = wallGradientFormula constructionSquare 2 3 3 19 := gapGradient_wall T constructionSquare 2 3 3 19
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 19 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 19 := rfl

theorem row09_alias0_coordinate_20 : gapGradient T constructionSquare (Gap.wall 2 3 3) 20 = polynomialGradient 9 20 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 20 = wallGradientFormula constructionSquare 2 3 3 20 := gapGradient_wall T constructionSquare 2 3 3 20
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 20 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 20 := rfl

theorem row09_alias0_coordinate_21 : gapGradient T constructionSquare (Gap.wall 2 3 3) 21 = polynomialGradient 9 21 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 21 = wallGradientFormula constructionSquare 2 3 3 21 := gapGradient_wall T constructionSquare 2 3 3 21
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 21 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 21 := rfl

theorem row09_alias0_coordinate_22 : gapGradient T constructionSquare (Gap.wall 2 3 3) 22 = polynomialGradient 9 22 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 22 = wallGradientFormula constructionSquare 2 3 3 22 := gapGradient_wall T constructionSquare 2 3 3 22
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 22 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 22 := rfl

theorem row09_alias0_coordinate_23 : gapGradient T constructionSquare (Gap.wall 2 3 3) 23 = polynomialGradient 9 23 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 23 = wallGradientFormula constructionSquare 2 3 3 23 := gapGradient_wall T constructionSquare 2 3 3 23
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 23 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 23 := rfl

theorem row09_alias0_coordinate_24 : gapGradient T constructionSquare (Gap.wall 2 3 3) 24 = polynomialGradient 9 24 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 24 = wallGradientFormula constructionSquare 2 3 3 24 := gapGradient_wall T constructionSquare 2 3 3 24
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 24 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 24 := rfl

theorem row09_alias0_coordinate_25 : gapGradient T constructionSquare (Gap.wall 2 3 3) 25 = polynomialGradient 9 25 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 25 = wallGradientFormula constructionSquare 2 3 3 25 := gapGradient_wall T constructionSquare 2 3 3 25
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 25 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 25 := rfl

theorem row09_alias0_coordinate_26 : gapGradient T constructionSquare (Gap.wall 2 3 3) 26 = polynomialGradient 9 26 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 26 = wallGradientFormula constructionSquare 2 3 3 26 := gapGradient_wall T constructionSquare 2 3 3 26
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 26 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 26 := rfl

theorem row09_alias0_coordinate_27 : gapGradient T constructionSquare (Gap.wall 2 3 3) 27 = polynomialGradient 9 27 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 27 = wallGradientFormula constructionSquare 2 3 3 27 := gapGradient_wall T constructionSquare 2 3 3 27
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 27 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 27 := rfl

theorem row09_alias0_coordinate_28 : gapGradient T constructionSquare (Gap.wall 2 3 3) 28 = polynomialGradient 9 28 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 28 = wallGradientFormula constructionSquare 2 3 3 28 := gapGradient_wall T constructionSquare 2 3 3 28
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 28 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 28 := rfl

theorem row09_alias0_coordinate_29 : gapGradient T constructionSquare (Gap.wall 2 3 3) 29 = polynomialGradient 9 29 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 29 = wallGradientFormula constructionSquare 2 3 3 29 := gapGradient_wall T constructionSquare 2 3 3 29
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 29 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 29 := rfl

theorem row09_alias0_coordinate_30 : gapGradient T constructionSquare (Gap.wall 2 3 3) 30 = polynomialGradient 9 30 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 30 = wallGradientFormula constructionSquare 2 3 3 30 := gapGradient_wall T constructionSquare 2 3 3 30
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 30 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 30 := rfl

theorem row09_alias0_coordinate_31 : gapGradient T constructionSquare (Gap.wall 2 3 3) 31 = polynomialGradient 9 31 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 31 = wallGradientFormula constructionSquare 2 3 3 31 := gapGradient_wall T constructionSquare 2 3 3 31
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 31 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 31 := rfl

theorem row09_alias0_coordinate_32 : gapGradient T constructionSquare (Gap.wall 2 3 3) 32 = polynomialGradient 9 32 := by
  calc
    gapGradient T constructionSquare (Gap.wall 2 3 3) 32 = wallGradientFormula constructionSquare 2 3 3 32 := gapGradient_wall T constructionSquare 2 3 3 32
    _ = 0 := wallGradientFormula_zero constructionSquare 2 3 3 32 (by decide) (by decide) (by decide)
    _ = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := (polyEval_zero u).symm
    _ = polynomialGradient 9 32 := rfl

theorem row09_alias0_gradient : gapGradient T constructionSquare (Gap.wall 2 3 3) = polynomialGradient 9 := by
  funext j
  fin_cases j
  · exact row09_alias0_coordinate_00
  · exact row09_alias0_coordinate_01
  · exact row09_alias0_coordinate_02
  · exact row09_alias0_coordinate_03
  · exact row09_alias0_coordinate_04
  · exact row09_alias0_coordinate_05
  · exact row09_alias0_coordinate_06
  · exact row09_alias0_coordinate_07
  · exact row09_alias0_coordinate_08
  · exact row09_alias0_coordinate_09
  · exact row09_alias0_coordinate_10
  · exact row09_alias0_coordinate_11
  · exact row09_alias0_coordinate_12
  · exact row09_alias0_coordinate_13
  · exact row09_alias0_coordinate_14
  · exact row09_alias0_coordinate_15
  · exact row09_alias0_coordinate_16
  · exact row09_alias0_coordinate_17
  · exact row09_alias0_coordinate_18
  · exact row09_alias0_coordinate_19
  · exact row09_alias0_coordinate_20
  · exact row09_alias0_coordinate_21
  · exact row09_alias0_coordinate_22
  · exact row09_alias0_coordinate_23
  · exact row09_alias0_coordinate_24
  · exact row09_alias0_coordinate_25
  · exact row09_alias0_coordinate_26
  · exact row09_alias0_coordinate_27
  · exact row09_alias0_coordinate_28
  · exact row09_alias0_coordinate_29
  · exact row09_alias0_coordinate_30
  · exact row09_alias0_coordinate_31
  · exact row09_alias0_coordinate_32

theorem row09_aliases_tied (g : Gap) (hg : g ∈ rowAliases 9) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient 9 := by
  change g ∈ [Gap.wall 2 3 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact ⟨row09_alias0_zero, row09_alias0_gradient⟩

end
end ElevenSquare.Tasks.T06
