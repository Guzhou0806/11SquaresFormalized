import ElevenSquare.Tasks.T06.Data
import ElevenSquare.Tasks.T06.PolynomialData

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section

/-- The exact reduced coefficient vector shared by each row coordinate. -/
def gradientPolynomials (r : Fin 56) (j : Fin 33) : Fin 8 → ℚ :=
  Pending.T06.gradientCoefficients (Pending.T06.gradientClass r j)

def polynomialGradient (r : Fin 56) (j : Fin 33) : ℝ :=
  Pending.T06.polyEval (gradientPolynomials r j) u

end
end ElevenSquare.Tasks.T06
