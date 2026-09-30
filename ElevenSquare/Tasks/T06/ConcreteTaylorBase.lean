import ElevenSquare.Tasks.T06.AnalyticPacket
import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase
import ElevenSquare.Tasks.T06.Radii
import Mathlib.Tactic.NormNum

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section

theorem concrete_feature_curvature_bound (q : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (f : SeparationFeature) (v : Fin 4) (A L C : ℝ)
    (hr : ∀ j, 0 ≤ r j)
    (hA : |dot (featureCenterDifference q f) (featureNormal q f)| +
      |dot (featureCenterDifference q f) (perp (featureNormal q f))| ≤ A)
    (hL : |(featureNormal q f).1| + |(featureNormal q f).2| ≤ L)
    (hC : |dot (cornerOffset q f.other v) (featureNormal q f)| +
      |dot (perp (cornerOffset q f.other v)) (featureNormal q f)| ≤ C) :
    featureRectangleCurvature q r f v ≤
      (A+L*featureTranslationRadius r f)*(r (coordinate f.owner 2))^2 +
      2*(L*featureTranslationRadius r f)*r (coordinate f.owner 2) +
      C*(r (coordinate f.other 2)+r (coordinate f.owner 2))^2 := by
  have ht : 0 ≤ featureTranslationRadius r f := by
    unfold featureTranslationRadius
    exact add_nonneg (add_nonneg (hr _) (hr _)) (add_nonneg (hr _) (hr _))
  have hv : featureVelocityBound q r f ≤ L*featureTranslationRadius r f :=
    mul_le_mul_of_nonneg_right hL ht
  unfold featureRectangleCurvature
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_right (add_le_add hA hv) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv (by norm_num)) (hr _)
  · exact mul_le_mul_of_nonneg_right hC (sq_nonneg _)

theorem concrete_wall_curvature_bound (q : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (i : Owner) (v : Fin 4) (C : ℝ)
    (hC : |(cornerOffset q i v).1| + |(cornerOffset q i v).2| ≤ C) :
    wallRectangleCurvature q r i v ≤ C*(r (coordinate i 2))^2 := by
  exact mul_le_mul_of_nonneg_right hC (sq_nonneg _)

end
end ElevenSquare.Tasks.T06
