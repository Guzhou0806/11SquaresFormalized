import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch03
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 30; closed chart interval [7/128, 15/256]. -/
private theorem terminal30_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (7/128 : ℝ) ≤ t) (hthi : t ≤ (15/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal30CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal30CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal30CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal30CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal30CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal30CoreField, fieldScaleRat]

private theorem terminal30_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal30CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal30CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal30_core_orbit :
    terminal30CoreField = coreOrbitVertices
      (terminal30CoreField[0]'(by decide))
      (terminal30CoreField[1]'(by decide)) := by
  norm_num [terminal30CoreField, coreOrbitVertices, rotateQ]

theorem terminal30_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (7/128 : ℝ) ≤ t) (hthi : t ≤ (15/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal30CoreField.map qpointFieldNormalize)) q := by
  rw [terminal30_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal30_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal30_side_norm)

/-- Archived far15 terminal row 31; closed chart interval [15/256, 1/16]. -/
private theorem terminal31_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (15/256 : ℝ) ≤ t) (hthi : t ≤ (1/16 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal31CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal31CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal31CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal31CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal31CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal31CoreField, fieldScaleRat]

private theorem terminal31_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal31CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal31CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal31_core_orbit :
    terminal31CoreField = coreOrbitVertices
      (terminal31CoreField[0]'(by decide))
      (terminal31CoreField[1]'(by decide)) := by
  norm_num [terminal31CoreField, coreOrbitVertices, rotateQ]

theorem terminal31_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (15/256 : ℝ) ≤ t) (hthi : t ≤ (1/16 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal31CoreField.map qpointFieldNormalize)) q := by
  rw [terminal31_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal31_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal31_side_norm)

/-- Archived far15 terminal row 32; closed chart interval [1/16, 17/256]. -/
private theorem terminal32_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/16 : ℝ) ≤ t) (hthi : t ≤ (17/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal32CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal32CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal32CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal32CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal32CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal32CoreField, fieldScaleRat]

private theorem terminal32_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal32CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal32CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal32_core_orbit :
    terminal32CoreField = coreOrbitVertices
      (terminal32CoreField[0]'(by decide))
      (terminal32CoreField[1]'(by decide)) := by
  norm_num [terminal32CoreField, coreOrbitVertices, rotateQ]

theorem terminal32_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/16 : ℝ) ≤ t) (hthi : t ≤ (17/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal32CoreField.map qpointFieldNormalize)) q := by
  rw [terminal32_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal32_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal32_side_norm)

/-- Archived far15 terminal row 33; closed chart interval [17/256, 9/128]. -/
private theorem terminal33_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (17/256 : ℝ) ≤ t) (hthi : t ≤ (9/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal33CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal33CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal33CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal33CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal33CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal33CoreField, fieldScaleRat]

private theorem terminal33_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal33CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal33CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal33_core_orbit :
    terminal33CoreField = coreOrbitVertices
      (terminal33CoreField[0]'(by decide))
      (terminal33CoreField[1]'(by decide)) := by
  norm_num [terminal33CoreField, coreOrbitVertices, rotateQ]

theorem terminal33_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (17/256 : ℝ) ≤ t) (hthi : t ≤ (9/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal33CoreField.map qpointFieldNormalize)) q := by
  rw [terminal33_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal33_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal33_side_norm)

/-- Archived far15 terminal row 34; closed chart interval [9/128, 19/256]. -/
private theorem terminal34_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (9/128 : ℝ) ≤ t) (hthi : t ≤ (19/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal34CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal34CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal34CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal34CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal34CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal34CoreField, fieldScaleRat]

private theorem terminal34_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal34CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal34CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal34_core_orbit :
    terminal34CoreField = coreOrbitVertices
      (terminal34CoreField[0]'(by decide))
      (terminal34CoreField[1]'(by decide)) := by
  norm_num [terminal34CoreField, coreOrbitVertices, rotateQ]

theorem terminal34_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (9/128 : ℝ) ≤ t) (hthi : t ≤ (19/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal34CoreField.map qpointFieldNormalize)) q := by
  rw [terminal34_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal34_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal34_side_norm)

/-- Archived far15 terminal row 35; closed chart interval [19/256, 5/64]. -/
private theorem terminal35_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (19/256 : ℝ) ≤ t) (hthi : t ≤ (5/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal35CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal35CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal35CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal35CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal35CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal35CoreField, fieldScaleRat]

private theorem terminal35_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal35CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal35CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal35_core_orbit :
    terminal35CoreField = coreOrbitVertices
      (terminal35CoreField[0]'(by decide))
      (terminal35CoreField[1]'(by decide)) := by
  norm_num [terminal35CoreField, coreOrbitVertices, rotateQ]

theorem terminal35_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (19/256 : ℝ) ≤ t) (hthi : t ≤ (5/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal35CoreField.map qpointFieldNormalize)) q := by
  rw [terminal35_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal35_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal35_side_norm)

/-- Archived far15 terminal row 36; closed chart interval [5/64, 21/256]. -/
private theorem terminal36_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (5/64 : ℝ) ≤ t) (hthi : t ≤ (21/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal36CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal36CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal36CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal36CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal36CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal36CoreField, fieldScaleRat]

private theorem terminal36_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal36CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal36CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal36_core_orbit :
    terminal36CoreField = coreOrbitVertices
      (terminal36CoreField[0]'(by decide))
      (terminal36CoreField[1]'(by decide)) := by
  norm_num [terminal36CoreField, coreOrbitVertices, rotateQ]

theorem terminal36_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (5/64 : ℝ) ≤ t) (hthi : t ≤ (21/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal36CoreField.map qpointFieldNormalize)) q := by
  rw [terminal36_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal36_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal36_side_norm)

/-- Archived far15 terminal row 37; closed chart interval [21/256, 11/128]. -/
private theorem terminal37_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (21/256 : ℝ) ≤ t) (hthi : t ≤ (11/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal37CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal37CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal37CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal37CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal37CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal37CoreField, fieldScaleRat]

private theorem terminal37_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal37CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal37CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal37_core_orbit :
    terminal37CoreField = coreOrbitVertices
      (terminal37CoreField[0]'(by decide))
      (terminal37CoreField[1]'(by decide)) := by
  norm_num [terminal37CoreField, coreOrbitVertices, rotateQ]

theorem terminal37_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (21/256 : ℝ) ≤ t) (hthi : t ≤ (11/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal37CoreField.map qpointFieldNormalize)) q := by
  rw [terminal37_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal37_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal37_side_norm)

/-- Archived far15 terminal row 38; closed chart interval [11/128, 23/256]. -/
private theorem terminal38_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (11/128 : ℝ) ≤ t) (hthi : t ≤ (23/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal38CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal38CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal38CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal38CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal38CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal38CoreField, fieldScaleRat]

private theorem terminal38_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal38CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal38CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal38_core_orbit :
    terminal38CoreField = coreOrbitVertices
      (terminal38CoreField[0]'(by decide))
      (terminal38CoreField[1]'(by decide)) := by
  norm_num [terminal38CoreField, coreOrbitVertices, rotateQ]

theorem terminal38_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (11/128 : ℝ) ≤ t) (hthi : t ≤ (23/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal38CoreField.map qpointFieldNormalize)) q := by
  rw [terminal38_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal38_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal38_side_norm)

/-- Archived far15 terminal row 39; closed chart interval [23/256, 3/32]. -/
private theorem terminal39_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (23/256 : ℝ) ≤ t) (hthi : t ≤ (3/32 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal39CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal39CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal39CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal39CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal39CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal39CoreField, fieldScaleRat]

private theorem terminal39_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal39CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal39CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal39_core_orbit :
    terminal39CoreField = coreOrbitVertices
      (terminal39CoreField[0]'(by decide))
      (terminal39CoreField[1]'(by decide)) := by
  norm_num [terminal39CoreField, coreOrbitVertices, rotateQ]

theorem terminal39_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (23/256 : ℝ) ≤ t) (hthi : t ≤ (3/32 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal39CoreField.map qpointFieldNormalize)) q := by
  rw [terminal39_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal39_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal39_side_norm)

end
end ElevenSquare.Tasks.T07
