import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch02
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 20; closed chart interval [1/64, 5/256]. -/
private theorem terminal20_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/64 : ℝ) ≤ t) (hthi : t ≤ (5/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal20CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal20CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal20CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal20CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal20CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal20CoreField, fieldScaleRat]

private theorem terminal20_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal20CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal20CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal20_core_orbit :
    terminal20CoreField = coreOrbitVertices
      (terminal20CoreField[0]'(by decide))
      (terminal20CoreField[1]'(by decide)) := by
  norm_num [terminal20CoreField, coreOrbitVertices, rotateQ]

theorem terminal20_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/64 : ℝ) ≤ t) (hthi : t ≤ (5/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal20CoreField.map qpointFieldNormalize)) q := by
  rw [terminal20_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal20_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal20_side_norm)

/-- Archived far15 terminal row 21; closed chart interval [5/256, 3/128]. -/
private theorem terminal21_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (5/256 : ℝ) ≤ t) (hthi : t ≤ (3/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal21CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal21CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal21CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal21CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal21CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal21CoreField, fieldScaleRat]

private theorem terminal21_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal21CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal21CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal21_core_orbit :
    terminal21CoreField = coreOrbitVertices
      (terminal21CoreField[0]'(by decide))
      (terminal21CoreField[1]'(by decide)) := by
  norm_num [terminal21CoreField, coreOrbitVertices, rotateQ]

theorem terminal21_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (5/256 : ℝ) ≤ t) (hthi : t ≤ (3/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal21CoreField.map qpointFieldNormalize)) q := by
  rw [terminal21_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal21_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal21_side_norm)

/-- Archived far15 terminal row 22; closed chart interval [3/128, 7/256]. -/
private theorem terminal22_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3/128 : ℝ) ≤ t) (hthi : t ≤ (7/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal22CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal22CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal22CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal22CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal22CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal22CoreField, fieldScaleRat]

private theorem terminal22_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal22CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal22CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal22_core_orbit :
    terminal22CoreField = coreOrbitVertices
      (terminal22CoreField[0]'(by decide))
      (terminal22CoreField[1]'(by decide)) := by
  norm_num [terminal22CoreField, coreOrbitVertices, rotateQ]

theorem terminal22_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3/128 : ℝ) ≤ t) (hthi : t ≤ (7/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal22CoreField.map qpointFieldNormalize)) q := by
  rw [terminal22_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal22_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal22_side_norm)

/-- Archived far15 terminal row 23; closed chart interval [7/256, 1/32]. -/
private theorem terminal23_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (7/256 : ℝ) ≤ t) (hthi : t ≤ (1/32 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal23CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal23CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal23CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal23CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal23CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal23CoreField, fieldScaleRat]

private theorem terminal23_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal23CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal23CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal23_core_orbit :
    terminal23CoreField = coreOrbitVertices
      (terminal23CoreField[0]'(by decide))
      (terminal23CoreField[1]'(by decide)) := by
  norm_num [terminal23CoreField, coreOrbitVertices, rotateQ]

theorem terminal23_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (7/256 : ℝ) ≤ t) (hthi : t ≤ (1/32 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal23CoreField.map qpointFieldNormalize)) q := by
  rw [terminal23_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal23_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal23_side_norm)

/-- Archived far15 terminal row 24; closed chart interval [1/32, 9/256]. -/
private theorem terminal24_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/32 : ℝ) ≤ t) (hthi : t ≤ (9/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal24CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal24CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal24CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal24CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal24CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal24CoreField, fieldScaleRat]

private theorem terminal24_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal24CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal24CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal24_core_orbit :
    terminal24CoreField = coreOrbitVertices
      (terminal24CoreField[0]'(by decide))
      (terminal24CoreField[1]'(by decide)) := by
  norm_num [terminal24CoreField, coreOrbitVertices, rotateQ]

theorem terminal24_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/32 : ℝ) ≤ t) (hthi : t ≤ (9/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal24CoreField.map qpointFieldNormalize)) q := by
  rw [terminal24_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal24_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal24_side_norm)

/-- Archived far15 terminal row 25; closed chart interval [9/256, 5/128]. -/
private theorem terminal25_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (9/256 : ℝ) ≤ t) (hthi : t ≤ (5/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal25CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal25CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal25CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal25CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal25CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal25CoreField, fieldScaleRat]

private theorem terminal25_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal25CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal25CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal25_core_orbit :
    terminal25CoreField = coreOrbitVertices
      (terminal25CoreField[0]'(by decide))
      (terminal25CoreField[1]'(by decide)) := by
  norm_num [terminal25CoreField, coreOrbitVertices, rotateQ]

theorem terminal25_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (9/256 : ℝ) ≤ t) (hthi : t ≤ (5/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal25CoreField.map qpointFieldNormalize)) q := by
  rw [terminal25_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal25_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal25_side_norm)

/-- Archived far15 terminal row 26; closed chart interval [5/128, 11/256]. -/
private theorem terminal26_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (5/128 : ℝ) ≤ t) (hthi : t ≤ (11/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal26CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal26CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal26CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal26CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal26CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal26CoreField, fieldScaleRat]

private theorem terminal26_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal26CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal26CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal26_core_orbit :
    terminal26CoreField = coreOrbitVertices
      (terminal26CoreField[0]'(by decide))
      (terminal26CoreField[1]'(by decide)) := by
  norm_num [terminal26CoreField, coreOrbitVertices, rotateQ]

theorem terminal26_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (5/128 : ℝ) ≤ t) (hthi : t ≤ (11/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal26CoreField.map qpointFieldNormalize)) q := by
  rw [terminal26_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal26_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal26_side_norm)

/-- Archived far15 terminal row 27; closed chart interval [11/256, 3/64]. -/
private theorem terminal27_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (11/256 : ℝ) ≤ t) (hthi : t ≤ (3/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal27CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal27CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal27CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal27CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal27CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal27CoreField, fieldScaleRat]

private theorem terminal27_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal27CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal27CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal27_core_orbit :
    terminal27CoreField = coreOrbitVertices
      (terminal27CoreField[0]'(by decide))
      (terminal27CoreField[1]'(by decide)) := by
  norm_num [terminal27CoreField, coreOrbitVertices, rotateQ]

theorem terminal27_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (11/256 : ℝ) ≤ t) (hthi : t ≤ (3/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal27CoreField.map qpointFieldNormalize)) q := by
  rw [terminal27_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal27_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal27_side_norm)

/-- Archived far15 terminal row 28; closed chart interval [3/64, 13/256]. -/
private theorem terminal28_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3/64 : ℝ) ≤ t) (hthi : t ≤ (13/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal28CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal28CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal28CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal28CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal28CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal28CoreField, fieldScaleRat]

private theorem terminal28_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal28CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal28CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal28_core_orbit :
    terminal28CoreField = coreOrbitVertices
      (terminal28CoreField[0]'(by decide))
      (terminal28CoreField[1]'(by decide)) := by
  norm_num [terminal28CoreField, coreOrbitVertices, rotateQ]

theorem terminal28_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3/64 : ℝ) ≤ t) (hthi : t ≤ (13/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal28CoreField.map qpointFieldNormalize)) q := by
  rw [terminal28_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal28_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal28_side_norm)

/-- Archived far15 terminal row 29; closed chart interval [13/256, 7/128]. -/
private theorem terminal29_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (13/256 : ℝ) ≤ t) (hthi : t ≤ (7/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal29CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal29CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal29CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal29CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal29CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal29CoreField, fieldScaleRat]

private theorem terminal29_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal29CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal29CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal29_core_orbit :
    terminal29CoreField = coreOrbitVertices
      (terminal29CoreField[0]'(by decide))
      (terminal29CoreField[1]'(by decide)) := by
  norm_num [terminal29CoreField, coreOrbitVertices, rotateQ]

theorem terminal29_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (13/256 : ℝ) ≤ t) (hthi : t ≤ (7/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal29CoreField.map qpointFieldNormalize)) q := by
  rw [terminal29_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal29_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal29_side_norm)

end
end ElevenSquare.Tasks.T07
