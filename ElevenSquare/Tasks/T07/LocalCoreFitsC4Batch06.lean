import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch06
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 240; closed chart interval [125613/127232, 62991/63616]. -/
private theorem terminal240_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (125613/127232 : ℝ) ≤ t) (hthi : t ≤ (62991/63616 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal240CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal240CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal240CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal240CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal240CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal240CoreField, fieldScaleRat]

private theorem terminal240_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal240CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal240CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal240_core_orbit :
    terminal240CoreField = coreOrbitVertices
      (terminal240CoreField[0]'(by decide))
      (terminal240CoreField[1]'(by decide)) := by
  norm_num [terminal240CoreField, coreOrbitVertices, rotateQ]

theorem terminal240_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (125613/127232 : ℝ) ≤ t) (hthi : t ≤ (62991/63616 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal240CoreField.map qpointFieldNormalize)) q := by
  rw [terminal240_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal240_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal240_side_norm)

/-- Archived far15 terminal row 241; closed chart interval [62991/63616, 126351/127232]. -/
private theorem terminal241_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (62991/63616 : ℝ) ≤ t) (hthi : t ≤ (126351/127232 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal241CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal241CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal241CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal241CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal241CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal241CoreField, fieldScaleRat]

private theorem terminal241_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal241CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal241CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal241_core_orbit :
    terminal241CoreField = coreOrbitVertices
      (terminal241CoreField[0]'(by decide))
      (terminal241CoreField[1]'(by decide)) := by
  norm_num [terminal241CoreField, coreOrbitVertices, rotateQ]

theorem terminal241_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (62991/63616 : ℝ) ≤ t) (hthi : t ≤ (126351/127232 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal241CoreField.map qpointFieldNormalize)) q := by
  rw [terminal241_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal241_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal241_side_norm)

/-- Archived far15 terminal row 242; closed chart interval [126351/127232, 495/497]. -/
private theorem terminal242_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (126351/127232 : ℝ) ≤ t) (hthi : t ≤ (495/497 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal242CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal242CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal242CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal242CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal242CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal242CoreField, fieldScaleRat]

private theorem terminal242_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal242CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal242CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal242_core_orbit :
    terminal242CoreField = coreOrbitVertices
      (terminal242CoreField[0]'(by decide))
      (terminal242CoreField[1]'(by decide)) := by
  norm_num [terminal242CoreField, coreOrbitVertices, rotateQ]

theorem terminal242_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (126351/127232 : ℝ) ≤ t) (hthi : t ≤ (495/497 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal242CoreField.map qpointFieldNormalize)) q := by
  rw [terminal242_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal242_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal242_side_norm)

/-- Archived far15 terminal row 243; closed chart interval [495/497, 3961/3976]. -/
private theorem terminal243_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (495/497 : ℝ) ≤ t) (hthi : t ≤ (3961/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal243CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal243CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal243CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal243CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal243CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal243CoreField, fieldScaleRat]

private theorem terminal243_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal243CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal243CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal243_core_orbit :
    terminal243CoreField = coreOrbitVertices
      (terminal243CoreField[0]'(by decide))
      (terminal243CoreField[1]'(by decide)) := by
  norm_num [terminal243CoreField, coreOrbitVertices, rotateQ]

theorem terminal243_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (495/497 : ℝ) ≤ t) (hthi : t ≤ (3961/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal243CoreField.map qpointFieldNormalize)) q := by
  rw [terminal243_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal243_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal243_side_norm)

/-- Archived far15 terminal row 244; closed chart interval [3961/3976, 283/284]. -/
private theorem terminal244_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3961/3976 : ℝ) ≤ t) (hthi : t ≤ (283/284 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal244CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal244CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal244CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal244CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal244CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal244CoreField, fieldScaleRat]

private theorem terminal244_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal244CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal244CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal244_core_orbit :
    terminal244CoreField = coreOrbitVertices
      (terminal244CoreField[0]'(by decide))
      (terminal244CoreField[1]'(by decide)) := by
  norm_num [terminal244CoreField, coreOrbitVertices, rotateQ]

theorem terminal244_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3961/3976 : ℝ) ≤ t) (hthi : t ≤ (283/284 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal244CoreField.map qpointFieldNormalize)) q := by
  rw [terminal244_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal244_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal244_side_norm)

/-- Archived far15 terminal row 245; closed chart interval [283/284, 3963/3976]. -/
private theorem terminal245_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (283/284 : ℝ) ≤ t) (hthi : t ≤ (3963/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal245CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal245CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal245CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal245CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal245CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal245CoreField, fieldScaleRat]

private theorem terminal245_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal245CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal245CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal245_core_orbit :
    terminal245CoreField = coreOrbitVertices
      (terminal245CoreField[0]'(by decide))
      (terminal245CoreField[1]'(by decide)) := by
  norm_num [terminal245CoreField, coreOrbitVertices, rotateQ]

theorem terminal245_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (283/284 : ℝ) ≤ t) (hthi : t ≤ (3963/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal245CoreField.map qpointFieldNormalize)) q := by
  rw [terminal245_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal245_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal245_side_norm)

/-- Archived far15 terminal row 246; closed chart interval [3963/3976, 991/994]. -/
private theorem terminal246_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3963/3976 : ℝ) ≤ t) (hthi : t ≤ (991/994 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal246CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal246CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal246CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal246CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal246CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal246CoreField, fieldScaleRat]

private theorem terminal246_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal246CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal246CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal246_core_orbit :
    terminal246CoreField = coreOrbitVertices
      (terminal246CoreField[0]'(by decide))
      (terminal246CoreField[1]'(by decide)) := by
  norm_num [terminal246CoreField, coreOrbitVertices, rotateQ]

theorem terminal246_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3963/3976 : ℝ) ≤ t) (hthi : t ≤ (991/994 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal246CoreField.map qpointFieldNormalize)) q := by
  rw [terminal246_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal246_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal246_side_norm)

/-- Archived far15 terminal row 247; closed chart interval [991/994, 3965/3976]. -/
private theorem terminal247_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (991/994 : ℝ) ≤ t) (hthi : t ≤ (3965/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal247CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal247CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal247CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal247CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal247CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal247CoreField, fieldScaleRat]

private theorem terminal247_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal247CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal247CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal247_core_orbit :
    terminal247CoreField = coreOrbitVertices
      (terminal247CoreField[0]'(by decide))
      (terminal247CoreField[1]'(by decide)) := by
  norm_num [terminal247CoreField, coreOrbitVertices, rotateQ]

theorem terminal247_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (991/994 : ℝ) ≤ t) (hthi : t ≤ (3965/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal247CoreField.map qpointFieldNormalize)) q := by
  rw [terminal247_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal247_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal247_side_norm)

/-- Archived far15 terminal row 248; closed chart interval [3965/3976, 1983/1988]. -/
private theorem terminal248_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3965/3976 : ℝ) ≤ t) (hthi : t ≤ (1983/1988 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal248CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal248CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal248CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal248CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal248CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal248CoreField, fieldScaleRat]

private theorem terminal248_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal248CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal248CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal248_core_orbit :
    terminal248CoreField = coreOrbitVertices
      (terminal248CoreField[0]'(by decide))
      (terminal248CoreField[1]'(by decide)) := by
  norm_num [terminal248CoreField, coreOrbitVertices, rotateQ]

theorem terminal248_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3965/3976 : ℝ) ≤ t) (hthi : t ≤ (1983/1988 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal248CoreField.map qpointFieldNormalize)) q := by
  rw [terminal248_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal248_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal248_side_norm)

/-- Archived far15 terminal row 249; closed chart interval [1983/1988, 3967/3976]. -/
private theorem terminal249_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1983/1988 : ℝ) ≤ t) (hthi : t ≤ (3967/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal249CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal249CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal249CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal249CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal249CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal249CoreField, fieldScaleRat]

private theorem terminal249_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal249CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal249CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal249_core_orbit :
    terminal249CoreField = coreOrbitVertices
      (terminal249CoreField[0]'(by decide))
      (terminal249CoreField[1]'(by decide)) := by
  norm_num [terminal249CoreField, coreOrbitVertices, rotateQ]

theorem terminal249_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1983/1988 : ℝ) ≤ t) (hthi : t ≤ (3967/3976 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal249CoreField.map qpointFieldNormalize)) q := by
  rw [terminal249_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal249_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal249_side_norm)

end
end ElevenSquare.Tasks.T07
