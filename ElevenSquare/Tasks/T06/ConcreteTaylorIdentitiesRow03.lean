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

theorem concreteRow03Alias0_C0 :
    (cornerOffset constructionSquare 0 1).1 = polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    (cornerOffset constructionSquare 0 1).1 - polyEval ![(1 / 2), 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

theorem concreteRow03Alias0_C1 :
    (cornerOffset constructionSquare 0 1).2 = polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u := by
  apply sub_eq_zero.mp
  calc
    (cornerOffset constructionSquare 0 1).2 - polyEval ![(-1 / 2), 0, 0, 0, 0, 0, 0, 0] u =
      0 * endpointPolynomial u := by
        norm_num [featureCenterDifference, featureNormal, cornerOffset, polyEval_vec, cornerSigns, constructionAxis, constructionCos, constructionSin, perp, dot, endpointPolynomial] <;> ring
    _ = 0 := by rw [u_polynomial, mul_zero]

end
end ElevenSquare.Tasks.T06
