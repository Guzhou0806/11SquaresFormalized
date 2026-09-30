import ElevenSquare.Tasks.T06.PolynomialEnclosure00
import ElevenSquare.Tasks.T06.PolynomialEnclosure01
import ElevenSquare.Tasks.T06.PolynomialEnclosure02
import ElevenSquare.Tasks.T06.PolynomialEnclosure03
import ElevenSquare.Tasks.T06.PolynomialEnclosure04
import ElevenSquare.Tasks.T06.PolynomialEnclosure05
import ElevenSquare.Tasks.T06.PolynomialEnclosure06
import ElevenSquare.Tasks.T06.PolynomialEnclosure07
import ElevenSquare.Tasks.T06.PolynomialEnclosure08
import ElevenSquare.Tasks.T06.PolynomialEnclosure09
import ElevenSquare.Tasks.T06.PolynomialEnclosure10
import ElevenSquare.Tasks.T06.PolynomialEnclosure11
import ElevenSquare.Tasks.T06.PolynomialEnclosure12
import ElevenSquare.Tasks.T06.PolynomialEnclosure13
import ElevenSquare.Tasks.T06.PolynomialEnclosure14
import ElevenSquare.Tasks.T06.PolynomialEnclosure15
import ElevenSquare.Tasks.T06.PolynomialEnclosure16
import ElevenSquare.Tasks.T06.PolynomialEnclosure17
import ElevenSquare.Tasks.T06.PolynomialEnclosure18
import ElevenSquare.Tasks.T06.PolynomialEnclosure19
import ElevenSquare.Tasks.T06.PolynomialEnclosure20
import ElevenSquare.Tasks.T06.PolynomialEnclosure21
import ElevenSquare.Tasks.T06.PolynomialEnclosure22
import ElevenSquare.Tasks.T06.PolynomialEnclosure23
import ElevenSquare.Tasks.T06.DataGradients
import ElevenSquare.Tasks.T06.Data
import Mathlib.Tactic.FinCases

namespace ElevenSquare.Pending.T06
noncomputable section

theorem gradient_error (k : Fin 24) :
    |polyEval (gradientCoefficients k) u - gradientRounded k| ≤ (1/1000000000000 : ℝ) := by
  fin_cases k
  · exact gradient_error_00
  · exact gradient_error_01
  · exact gradient_error_02
  · exact gradient_error_03
  · exact gradient_error_04
  · exact gradient_error_05
  · exact gradient_error_06
  · exact gradient_error_07
  · exact gradient_error_08
  · exact gradient_error_09
  · exact gradient_error_10
  · exact gradient_error_11
  · exact gradient_error_12
  · exact gradient_error_13
  · exact gradient_error_14
  · exact gradient_error_15
  · exact gradient_error_16
  · exact gradient_error_17
  · exact gradient_error_18
  · exact gradient_error_19
  · exact gradient_error_20
  · exact gradient_error_21
  · exact gradient_error_22
  · exact gradient_error_23

end
end ElevenSquare.Pending.T06

namespace ElevenSquare.Tasks.T06
open ElevenSquare.Pending.T06
noncomputable section

theorem polynomialGradient_error (r : Fin 56) (j : Fin 33) :
    |polynomialGradient r j - (roundedGradients r j : ℝ)/1000000000000| ≤
      (1/1000000000000 : ℝ) := by
  simpa [polynomialGradient, gradientPolynomials, roundedGradients, gradientRounded]
    using gradient_error (gradientClass r j)

end
end ElevenSquare.Tasks.T06
