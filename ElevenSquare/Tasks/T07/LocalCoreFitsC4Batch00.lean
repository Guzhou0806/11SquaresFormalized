import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch00
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 0; closed chart interval [0, 1/7936]. -/
private theorem terminal0_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (0 : ℝ) ≤ t) (hthi : t ≤ (1/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal0CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal0CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal0CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal0CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal0CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal0CoreField, fieldScaleRat]

private theorem terminal0_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal0CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal0CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal0_core_orbit :
    terminal0CoreField = coreOrbitVertices
      (terminal0CoreField[0]'(by decide))
      (terminal0CoreField[1]'(by decide)) := by
  norm_num [terminal0CoreField, coreOrbitVertices, rotateQ]

theorem terminal0_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (0 : ℝ) ≤ t) (hthi : t ≤ (1/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal0CoreField.map qpointFieldNormalize)) q := by
  rw [terminal0_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal0_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal0_side_norm)

/-- Archived far15 terminal row 2; closed chart interval [1/3968, 3/7936]. -/
private theorem terminal2_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/3968 : ℝ) ≤ t) (hthi : t ≤ (3/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal2CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal2CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal2CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal2CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal2CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal2CoreField, fieldScaleRat]

private theorem terminal2_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal2CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal2CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal2_core_orbit :
    terminal2CoreField = coreOrbitVertices
      (terminal2CoreField[0]'(by decide))
      (terminal2CoreField[1]'(by decide)) := by
  norm_num [terminal2CoreField, coreOrbitVertices, rotateQ]

theorem terminal2_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/3968 : ℝ) ≤ t) (hthi : t ≤ (3/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal2CoreField.map qpointFieldNormalize)) q := by
  rw [terminal2_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal2_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal2_side_norm)

/-- Archived far15 terminal row 3; closed chart interval [3/7936, 1/1984]. -/
private theorem terminal3_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3/7936 : ℝ) ≤ t) (hthi : t ≤ (1/1984 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal3CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal3CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal3CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal3CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal3CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal3CoreField, fieldScaleRat]

private theorem terminal3_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal3CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal3CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal3_core_orbit :
    terminal3CoreField = coreOrbitVertices
      (terminal3CoreField[0]'(by decide))
      (terminal3CoreField[1]'(by decide)) := by
  norm_num [terminal3CoreField, coreOrbitVertices, rotateQ]

theorem terminal3_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3/7936 : ℝ) ≤ t) (hthi : t ≤ (1/1984 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal3CoreField.map qpointFieldNormalize)) q := by
  rw [terminal3_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal3_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal3_side_norm)

/-- Archived far15 terminal row 4; closed chart interval [1/1984, 5/7936]. -/
private theorem terminal4_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/1984 : ℝ) ≤ t) (hthi : t ≤ (5/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal4CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal4CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal4CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal4CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal4CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal4CoreField, fieldScaleRat]

private theorem terminal4_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal4CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal4CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal4_core_orbit :
    terminal4CoreField = coreOrbitVertices
      (terminal4CoreField[0]'(by decide))
      (terminal4CoreField[1]'(by decide)) := by
  norm_num [terminal4CoreField, coreOrbitVertices, rotateQ]

theorem terminal4_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/1984 : ℝ) ≤ t) (hthi : t ≤ (5/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal4CoreField.map qpointFieldNormalize)) q := by
  rw [terminal4_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal4_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal4_side_norm)

/-- Archived far15 terminal row 5; closed chart interval [5/7936, 3/3968]. -/
private theorem terminal5_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (5/7936 : ℝ) ≤ t) (hthi : t ≤ (3/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal5CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal5CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal5CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal5CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal5CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal5CoreField, fieldScaleRat]

private theorem terminal5_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal5CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal5CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal5_core_orbit :
    terminal5CoreField = coreOrbitVertices
      (terminal5CoreField[0]'(by decide))
      (terminal5CoreField[1]'(by decide)) := by
  norm_num [terminal5CoreField, coreOrbitVertices, rotateQ]

theorem terminal5_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (5/7936 : ℝ) ≤ t) (hthi : t ≤ (3/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal5CoreField.map qpointFieldNormalize)) q := by
  rw [terminal5_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal5_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal5_side_norm)

/-- Archived far15 terminal row 6; closed chart interval [3/3968, 7/7936]. -/
private theorem terminal6_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3/3968 : ℝ) ≤ t) (hthi : t ≤ (7/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal6CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal6CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal6CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal6CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal6CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal6CoreField, fieldScaleRat]

private theorem terminal6_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal6CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal6CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal6_core_orbit :
    terminal6CoreField = coreOrbitVertices
      (terminal6CoreField[0]'(by decide))
      (terminal6CoreField[1]'(by decide)) := by
  norm_num [terminal6CoreField, coreOrbitVertices, rotateQ]

theorem terminal6_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3/3968 : ℝ) ≤ t) (hthi : t ≤ (7/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal6CoreField.map qpointFieldNormalize)) q := by
  rw [terminal6_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal6_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal6_side_norm)

/-- Archived far15 terminal row 7; closed chart interval [7/7936, 1/992]. -/
private theorem terminal7_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (7/7936 : ℝ) ≤ t) (hthi : t ≤ (1/992 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal7CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal7CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal7CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal7CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal7CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal7CoreField, fieldScaleRat]

private theorem terminal7_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal7CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal7CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal7_core_orbit :
    terminal7CoreField = coreOrbitVertices
      (terminal7CoreField[0]'(by decide))
      (terminal7CoreField[1]'(by decide)) := by
  norm_num [terminal7CoreField, coreOrbitVertices, rotateQ]

theorem terminal7_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (7/7936 : ℝ) ≤ t) (hthi : t ≤ (1/992 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal7CoreField.map qpointFieldNormalize)) q := by
  rw [terminal7_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal7_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal7_side_norm)

/-- Archived far15 terminal row 8; closed chart interval [1/992, 9/7936]. -/
private theorem terminal8_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/992 : ℝ) ≤ t) (hthi : t ≤ (9/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal8CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal8CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal8CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal8CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal8CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal8CoreField, fieldScaleRat]

private theorem terminal8_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal8CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal8CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal8_core_orbit :
    terminal8CoreField = coreOrbitVertices
      (terminal8CoreField[0]'(by decide))
      (terminal8CoreField[1]'(by decide)) := by
  norm_num [terminal8CoreField, coreOrbitVertices, rotateQ]

theorem terminal8_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/992 : ℝ) ≤ t) (hthi : t ≤ (9/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal8CoreField.map qpointFieldNormalize)) q := by
  rw [terminal8_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal8_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal8_side_norm)

/-- Archived far15 terminal row 9; closed chart interval [9/7936, 5/3968]. -/
private theorem terminal9_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (9/7936 : ℝ) ≤ t) (hthi : t ≤ (5/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal9CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal9CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal9CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal9CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal9CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal9CoreField, fieldScaleRat]

private theorem terminal9_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal9CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal9CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal9_core_orbit :
    terminal9CoreField = coreOrbitVertices
      (terminal9CoreField[0]'(by decide))
      (terminal9CoreField[1]'(by decide)) := by
  norm_num [terminal9CoreField, coreOrbitVertices, rotateQ]

theorem terminal9_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (9/7936 : ℝ) ≤ t) (hthi : t ≤ (5/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal9CoreField.map qpointFieldNormalize)) q := by
  rw [terminal9_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal9_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal9_side_norm)

end
end ElevenSquare.Tasks.T07
