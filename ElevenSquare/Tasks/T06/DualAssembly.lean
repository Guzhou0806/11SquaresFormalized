import ElevenSquare.Tasks.T06.CertificateBridge
import ElevenSquare.Tasks.T06.DataPacket

namespace ElevenSquare.Tasks.T06

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open ElevenSquare ElevenSquare.Pending

noncomputable section

theorem proposedPacket_radii_eq_coe (j : Fin 33) :
    proposedPacket.radii j = (coordinateRadiiQ j : ℝ) := by
  fin_cases j <;> norm_num [proposedPacket, focusedRadii, coordinateRadiiQ]

theorem proposedPacket_maxRadius_eq_coe :
    proposedPacket.maxRadius = (maxRadiusQ : ℝ) := by
  norm_num [proposedPacket, proposedMaxRadius, maxRadiusQ]

theorem coordinateRadiiQ_bounds (j : Fin 33) :
    0 < coordinateRadiiQ j ∧ coordinateRadiiQ j ≤ maxRadiusQ ∧
      coordinateRadiiQ j ≤ 1 / 64 := by
  fin_cases j <;> norm_num [coordinateRadiiQ, maxRadiusQ]

theorem proposedPacket_curvature_nonneg (b : Fin 128) (i : Fin 42) :
    0 ≤ proposedPacket.curvature b i := by
  change 0 ≤ rowCurvatures (branchRows b i)
  rw [rowCurvatures_eq_scaled_numerators]
  positivity

/-- Concrete dual assembly.  The three finite premises are supplied by the
integer shards and their equality with the original residual proposals; the
last premise is the enclosure of the actual algebraic gradients. -/
theorem proposedPacket_dualBounds_of_integer_checks
    (S : ℝ) (q₀ : Owner → UnitSquare)
    (hres : ∀ b j s, integerResidualCheck b j s (dualNumerators b j s))
    (hmass : ∀ b j s, integerMassCheck b j s (dualNumerators b j s))
    (heps : ∀ b j s, residualBounds b j s =
      (residualNumerators b j s : ℚ) / 1000000000000000000000000)
    (hgradient : ∀ r k,
      |gapGradient S q₀ (representatives r) k -
        (((roundedGradients r k : ℚ) / 1000000000000 : ℚ) : ℝ)| ≤
        ((1 / 1000000000000 : ℚ) : ℝ)) :
    DualBounds S q₀ proposedPacket := by
  apply dualBounds_of_rational_checks S q₀ proposedPacket
    coordinateRadiiQ maxRadiusQ (1 / 1000000000000) certificateMatrix
    proposedPacket_radii_eq_coe proposedPacket_maxRadius_eq_coe
    coordinateRadiiQ_bounds
  · norm_num [maxRadiusQ]
  · exact proposedPacket_curvature_nonneg
  · exact proposedPacket_dual_nonneg
  · intro b j s
    change 0 ≤ residualBounds b j s
    rw [heps]
    positivity
  · intro b i k
    simpa only [proposedPacket, certificateMatrix] using hgradient (branchRows b i) k
  · intro b j s
    have h := rational_residual_of_integer b j s (dualNumerators b j s) (hres b j s)
    simpa only [proposedPacket, certificateResidualCheck, certificateWeight, dualSignQ, heps] using h
  · intro b j s
    have h := rational_mass_of_integer b j s (dualNumerators b j s) (hmass b j s)
    simpa only [proposedPacket, certificateMassCheck, certificateWeight, heps] using h

end
end ElevenSquare.Tasks.T06
