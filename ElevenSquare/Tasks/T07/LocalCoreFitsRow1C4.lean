import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch00
import Mathlib.Tactic.NormNum

/-! Two-seed certificate for the archived terminal row 1 core. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

private theorem terminal1_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/7936 : ℝ) ≤ t) (hthi : t ≤ (1/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal1CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal1CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal1CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal1CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal1CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal1CoreField, fieldScaleRat]

private theorem terminal1_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal1CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal1CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal1_core_orbit :
    terminal1CoreField = coreOrbitVertices
      (terminal1CoreField[0]'(by decide))
      (terminal1CoreField[1]'(by decide)) := by
  norm_num [terminal1CoreField, coreOrbitVertices, rotateQ]

theorem terminal1_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/7936 : ℝ) ≤ t) (hthi : t ≤ (1/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal1CoreField.map qpointFieldNormalize)) q := by
  rw [terminal1_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal1_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal1_side_norm)

end
end ElevenSquare.Tasks.T07
