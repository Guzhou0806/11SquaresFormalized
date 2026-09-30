import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch07
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 250; closed chart interval [3967/3976, 496/497]. -/
private theorem terminal250_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3967/3976 : ℝ) ≤ t) (hthi : t ≤ (496/497 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal250CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal250CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal250CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal250CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal250CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal250CoreField, fieldScaleRat]

private theorem terminal250_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal250CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal250CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal250_core_orbit :
    terminal250CoreField = coreOrbitVertices
      (terminal250CoreField[0]'(by decide))
      (terminal250CoreField[1]'(by decide)) := by
  norm_num [terminal250CoreField, coreOrbitVertices, rotateQ]

theorem terminal250_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3967/3976 : ℝ) ≤ t) (hthi : t ≤ (496/497 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal250CoreField.map qpointFieldNormalize)) q := by
  rw [terminal250_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal250_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal250_side_norm)

/-- Archived far15 terminal row 251; closed chart interval [496/497, 567/568]. -/
private theorem terminal251_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (496/497 : ℝ) ≤ t) (hthi : t ≤ (567/568 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal251CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal251CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal251CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal251CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal251CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal251CoreField, fieldScaleRat]

private theorem terminal251_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal251CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal251CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal251_core_orbit :
    terminal251CoreField = coreOrbitVertices
      (terminal251CoreField[0]'(by decide))
      (terminal251CoreField[1]'(by decide)) := by
  norm_num [terminal251CoreField, coreOrbitVertices, rotateQ]

theorem terminal251_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (496/497 : ℝ) ≤ t) (hthi : t ≤ (567/568 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal251CoreField.map qpointFieldNormalize)) q := by
  rw [terminal251_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal251_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal251_side_norm)

/-- Archived far15 terminal row 252; closed chart interval [567/568, 1985/1988]. -/
private theorem terminal252_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (567/568 : ℝ) ≤ t) (hthi : t ≤ (1985/1988 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal252CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal252CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal252CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal252CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal252CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal252CoreField, fieldScaleRat]

private theorem terminal252_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal252CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal252CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal252_core_orbit :
    terminal252CoreField = coreOrbitVertices
      (terminal252CoreField[0]'(by decide))
      (terminal252CoreField[1]'(by decide)) := by
  norm_num [terminal252CoreField, coreOrbitVertices, rotateQ]

theorem terminal252_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (567/568 : ℝ) ≤ t) (hthi : t ≤ (1985/1988 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal252CoreField.map qpointFieldNormalize)) q := by
  rw [terminal252_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal252_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal252_side_norm)

/-- Archived far15 terminal row 253; closed chart interval [1985/1988, 3971/3976]. -/
private theorem terminal253_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1985/1988 : ℝ) ≤ t) (hthi : t ≤ (3971/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal253CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal253CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal253CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal253CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal253CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal253CoreField, fieldScaleRat]

private theorem terminal253_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal253CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal253CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal253_core_orbit :
    terminal253CoreField = coreOrbitVertices
      (terminal253CoreField[0]'(by decide))
      (terminal253CoreField[1]'(by decide)) := by
  norm_num [terminal253CoreField, coreOrbitVertices, rotateQ]

theorem terminal253_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1985/1988 : ℝ) ≤ t) (hthi : t ≤ (3971/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal253CoreField.map qpointFieldNormalize)) q := by
  rw [terminal253_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal253_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal253_side_norm)

/-- Archived far15 terminal row 254; closed chart interval [3971/3976, 993/994]. -/
private theorem terminal254_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3971/3976 : ℝ) ≤ t) (hthi : t ≤ (993/994 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal254CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal254CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal254CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal254CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal254CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal254CoreField, fieldScaleRat]

private theorem terminal254_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal254CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal254CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal254_core_orbit :
    terminal254CoreField = coreOrbitVertices
      (terminal254CoreField[0]'(by decide))
      (terminal254CoreField[1]'(by decide)) := by
  norm_num [terminal254CoreField, coreOrbitVertices, rotateQ]

theorem terminal254_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3971/3976 : ℝ) ≤ t) (hthi : t ≤ (993/994 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal254CoreField.map qpointFieldNormalize)) q := by
  rw [terminal254_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal254_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal254_side_norm)

/-- Archived far15 terminal row 255; closed chart interval [993/994, 3973/3976]. -/
private theorem terminal255_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (993/994 : ℝ) ≤ t) (hthi : t ≤ (3973/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal255CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal255CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal255CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal255CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal255CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal255CoreField, fieldScaleRat]

private theorem terminal255_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal255CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal255CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal255_core_orbit :
    terminal255CoreField = coreOrbitVertices
      (terminal255CoreField[0]'(by decide))
      (terminal255CoreField[1]'(by decide)) := by
  norm_num [terminal255CoreField, coreOrbitVertices, rotateQ]

theorem terminal255_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (993/994 : ℝ) ≤ t) (hthi : t ≤ (3973/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal255CoreField.map qpointFieldNormalize)) q := by
  rw [terminal255_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal255_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal255_side_norm)

/-- Archived far15 terminal row 256; closed chart interval [3973/3976, 1987/1988]. -/
private theorem terminal256_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3973/3976 : ℝ) ≤ t) (hthi : t ≤ (1987/1988 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal256CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal256CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal256CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal256CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal256CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal256CoreField, fieldScaleRat]

private theorem terminal256_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal256CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal256CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal256_core_orbit :
    terminal256CoreField = coreOrbitVertices
      (terminal256CoreField[0]'(by decide))
      (terminal256CoreField[1]'(by decide)) := by
  norm_num [terminal256CoreField, coreOrbitVertices, rotateQ]

theorem terminal256_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3973/3976 : ℝ) ≤ t) (hthi : t ≤ (1987/1988 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal256CoreField.map qpointFieldNormalize)) q := by
  rw [terminal256_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal256_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal256_side_norm)

/-- Archived far15 terminal row 257; closed chart interval [1987/1988, 3975/3976]. -/
private theorem terminal257_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1987/1988 : ℝ) ≤ t) (hthi : t ≤ (3975/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal257CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal257CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal257CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal257CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal257CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal257CoreField, fieldScaleRat]

private theorem terminal257_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal257CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal257CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal257_core_orbit :
    terminal257CoreField = coreOrbitVertices
      (terminal257CoreField[0]'(by decide))
      (terminal257CoreField[1]'(by decide)) := by
  norm_num [terminal257CoreField, coreOrbitVertices, rotateQ]

theorem terminal257_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1987/1988 : ℝ) ≤ t) (hthi : t ≤ (3975/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal257CoreField.map qpointFieldNormalize)) q := by
  rw [terminal257_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal257_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal257_side_norm)

/-- Archived far15 terminal row 258; closed chart interval [3975/3976, 1]. -/
private theorem terminal258_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3975/3976 : ℝ) ≤ t) (hthi : t ≤ (1 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal258CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal258CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal258CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal258CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal258CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal258CoreField, fieldScaleRat]

private theorem terminal258_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal258CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal258CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal258_core_orbit :
    terminal258CoreField = coreOrbitVertices
      (terminal258CoreField[0]'(by decide))
      (terminal258CoreField[1]'(by decide)) := by
  norm_num [terminal258CoreField, coreOrbitVertices, rotateQ]

theorem terminal258_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3975/3976 : ℝ) ≤ t) (hthi : t ≤ (1 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal258CoreField.map qpointFieldNormalize)) q := by
  rw [terminal258_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal258_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal258_side_norm)

end
end ElevenSquare.Tasks.T07
