import ElevenSquare.Tasks.T06.Certificates
import ElevenSquare.Tasks.T06.ResidualDataEquality
import ElevenSquare.Tasks.T06.DualAssembly
import ElevenSquare.Tasks.T06.GradientErrorBounds
import ElevenSquare.Tasks.T06.GradientsPacket
import ElevenSquare.Tasks.T06.ConcreteBranches
import ElevenSquare.Tasks.T06.ConcreteTaylorPacket

namespace ElevenSquare.Tasks.T06

open ElevenSquare ElevenSquare.Pending

noncomputable section

theorem actualGradient_error (r : Fin 56) (k : Fin 33) :
    |gapGradient T constructionSquare (representatives r) k -
      (((roundedGradients r k : ℚ) / 1000000000000 : ℚ) : ℝ)| ≤
      ((1 / 1000000000000 : ℚ) : ℝ) := by
  rw [representative_gradient]
  exact polynomialGradient_error_rational r k

theorem proposedPacket_dualBounds : DualBounds T constructionSquare proposedPacket :=
  proposedPacket_dualBounds_of_integer_checks T constructionSquare
    allIntegerResidualChecks allIntegerMassChecks allResidualData actualGradient_error

end
end ElevenSquare.Tasks.T06
