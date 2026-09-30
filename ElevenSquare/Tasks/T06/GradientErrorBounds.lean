import ElevenSquare.Tasks.T06.PolynomialEnclosures

namespace ElevenSquare.Tasks.T06

open ElevenSquare ElevenSquare.Pending

noncomputable section

theorem polynomialGradient_error_rational (r : Fin 56) (k : Fin 33) :
    |polynomialGradient r k -
      (((roundedGradients r k : ℚ) / 1000000000000 : ℚ) : ℝ)| ≤
      ((1 / 1000000000000 : ℚ) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, Rat.cast_one] using
    polynomialGradient_error r k

end
end ElevenSquare.Tasks.T06
