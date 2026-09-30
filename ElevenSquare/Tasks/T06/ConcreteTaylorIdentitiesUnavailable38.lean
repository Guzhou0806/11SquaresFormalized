import ElevenSquare.Tasks.T06.ConcreteTaylorGeometry
import ElevenSquare.Tasks.T06.GradientsConstruction
import ElevenSquare.Tasks.T06.GradientsPolynomial
import ElevenSquare.ConstructionData
import ElevenSquare.Tasks.T06.AnalyticPacket
import ElevenSquare.Tasks.T06.Gradients
import ElevenSquare.Tasks.T06.PolynomialBounds
import ElevenSquare.Tasks.T06.DataFeatures

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem concreteUnavailable38_A0 :
    dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) - polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem concreteUnavailable38_A1 :
    dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false }))) = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false }))) - polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem concreteUnavailable38_L0 :
    (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })).1 = polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })).1 - polyEval ![1, 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem concreteUnavailable38_L1 :
    (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })).2 = polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })).2 - polyEval ![0, 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem concreteUnavailable38_C0 :
    dot (cornerOffset constructionSquare 3 0) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    dot (cornerOffset constructionSquare 3 0) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) - polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem concreteUnavailable38_C1 :
    dot (perp (cornerOffset constructionSquare 3 0)) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    dot (perp (cornerOffset constructionSquare 3 0)) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false })) - polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem concreteUnavailable38_value :
    gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 = polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 - polyEval ![-1, 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [gapValue, featureGap, perturbedCorner, perturbedCenter, perturbedAxis, featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]


end
end ElevenSquare.Tasks.T06
