import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch01
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 10; closed chart interval [5/3968, 11/7936]. -/
private theorem terminal10_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (5/3968 : ℝ) ≤ t) (hthi : t ≤ (11/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal10CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal10CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal10CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal10CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal10CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal10CoreField, fieldScaleRat]

private theorem terminal10_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal10CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal10CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal10_core_orbit :
    terminal10CoreField = coreOrbitVertices
      (terminal10CoreField[0]'(by decide))
      (terminal10CoreField[1]'(by decide)) := by
  norm_num [terminal10CoreField, coreOrbitVertices, rotateQ]

theorem terminal10_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (5/3968 : ℝ) ≤ t) (hthi : t ≤ (11/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal10CoreField.map qpointFieldNormalize)) q := by
  rw [terminal10_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal10_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal10_side_norm)

/-- Archived far15 terminal row 11; closed chart interval [11/7936, 3/1984]. -/
private theorem terminal11_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (11/7936 : ℝ) ≤ t) (hthi : t ≤ (3/1984 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal11CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal11CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal11CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal11CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal11CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal11CoreField, fieldScaleRat]

private theorem terminal11_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal11CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal11CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal11_core_orbit :
    terminal11CoreField = coreOrbitVertices
      (terminal11CoreField[0]'(by decide))
      (terminal11CoreField[1]'(by decide)) := by
  norm_num [terminal11CoreField, coreOrbitVertices, rotateQ]

theorem terminal11_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (11/7936 : ℝ) ≤ t) (hthi : t ≤ (3/1984 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal11CoreField.map qpointFieldNormalize)) q := by
  rw [terminal11_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal11_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal11_side_norm)

/-- Archived far15 terminal row 12; closed chart interval [3/1984, 13/7936]. -/
private theorem terminal12_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (3/1984 : ℝ) ≤ t) (hthi : t ≤ (13/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal12CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal12CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal12CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal12CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal12CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal12CoreField, fieldScaleRat]

private theorem terminal12_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal12CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal12CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal12_core_orbit :
    terminal12CoreField = coreOrbitVertices
      (terminal12CoreField[0]'(by decide))
      (terminal12CoreField[1]'(by decide)) := by
  norm_num [terminal12CoreField, coreOrbitVertices, rotateQ]

theorem terminal12_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (3/1984 : ℝ) ≤ t) (hthi : t ≤ (13/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal12CoreField.map qpointFieldNormalize)) q := by
  rw [terminal12_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal12_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal12_side_norm)

/-- Archived far15 terminal row 13; closed chart interval [13/7936, 7/3968]. -/
private theorem terminal13_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (13/7936 : ℝ) ≤ t) (hthi : t ≤ (7/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal13CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal13CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal13CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal13CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal13CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal13CoreField, fieldScaleRat]

private theorem terminal13_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal13CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal13CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal13_core_orbit :
    terminal13CoreField = coreOrbitVertices
      (terminal13CoreField[0]'(by decide))
      (terminal13CoreField[1]'(by decide)) := by
  norm_num [terminal13CoreField, coreOrbitVertices, rotateQ]

theorem terminal13_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (13/7936 : ℝ) ≤ t) (hthi : t ≤ (7/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal13CoreField.map qpointFieldNormalize)) q := by
  rw [terminal13_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal13_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal13_side_norm)

/-- Archived far15 terminal row 14; closed chart interval [7/3968, 15/7936]. -/
private theorem terminal14_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (7/3968 : ℝ) ≤ t) (hthi : t ≤ (15/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal14CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal14CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal14CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal14CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal14CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal14CoreField, fieldScaleRat]

private theorem terminal14_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal14CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal14CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal14_core_orbit :
    terminal14CoreField = coreOrbitVertices
      (terminal14CoreField[0]'(by decide))
      (terminal14CoreField[1]'(by decide)) := by
  norm_num [terminal14CoreField, coreOrbitVertices, rotateQ]

theorem terminal14_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (7/3968 : ℝ) ≤ t) (hthi : t ≤ (15/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal14CoreField.map qpointFieldNormalize)) q := by
  rw [terminal14_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal14_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal14_side_norm)

/-- Archived far15 terminal row 15; closed chart interval [15/7936, 1/496]. -/
private theorem terminal15_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (15/7936 : ℝ) ≤ t) (hthi : t ≤ (1/496 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal15CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal15CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal15CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal15CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal15CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal15CoreField, fieldScaleRat]

private theorem terminal15_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal15CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal15CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal15_core_orbit :
    terminal15CoreField = coreOrbitVertices
      (terminal15CoreField[0]'(by decide))
      (terminal15CoreField[1]'(by decide)) := by
  norm_num [terminal15CoreField, coreOrbitVertices, rotateQ]

theorem terminal15_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (15/7936 : ℝ) ≤ t) (hthi : t ≤ (1/496 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal15CoreField.map qpointFieldNormalize)) q := by
  rw [terminal15_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal15_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal15_side_norm)

/-- Archived far15 terminal row 16; closed chart interval [1/496, 43/7936]. -/
private theorem terminal16_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (1/496 : ℝ) ≤ t) (hthi : t ≤ (43/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal16CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal16CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal16CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal16CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal16CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal16CoreField, fieldScaleRat]

private theorem terminal16_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal16CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal16CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal16_core_orbit :
    terminal16CoreField = coreOrbitVertices
      (terminal16CoreField[0]'(by decide))
      (terminal16CoreField[1]'(by decide)) := by
  norm_num [terminal16CoreField, coreOrbitVertices, rotateQ]

theorem terminal16_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (1/496 : ℝ) ≤ t) (hthi : t ≤ (43/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal16CoreField.map qpointFieldNormalize)) q := by
  rw [terminal16_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal16_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal16_side_norm)

/-- Archived far15 terminal row 17; closed chart interval [43/7936, 35/3968]. -/
private theorem terminal17_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (43/7936 : ℝ) ≤ t) (hthi : t ≤ (35/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal17CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal17CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal17CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal17CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal17CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal17CoreField, fieldScaleRat]

private theorem terminal17_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal17CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal17CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal17_core_orbit :
    terminal17CoreField = coreOrbitVertices
      (terminal17CoreField[0]'(by decide))
      (terminal17CoreField[1]'(by decide)) := by
  norm_num [terminal17CoreField, coreOrbitVertices, rotateQ]

theorem terminal17_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (43/7936 : ℝ) ≤ t) (hthi : t ≤ (35/3968 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal17CoreField.map qpointFieldNormalize)) q := by
  rw [terminal17_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal17_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal17_side_norm)

/-- Archived far15 terminal row 18; closed chart interval [35/3968, 97/7936]. -/
private theorem terminal18_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (35/3968 : ℝ) ≤ t) (hthi : t ≤ (97/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal18CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal18CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal18CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal18CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal18CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal18CoreField, fieldScaleRat]

private theorem terminal18_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal18CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal18CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal18_core_orbit :
    terminal18CoreField = coreOrbitVertices
      (terminal18CoreField[0]'(by decide))
      (terminal18CoreField[1]'(by decide)) := by
  norm_num [terminal18CoreField, coreOrbitVertices, rotateQ]

theorem terminal18_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (35/3968 : ℝ) ≤ t) (hthi : t ≤ (97/7936 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal18CoreField.map qpointFieldNormalize)) q := by
  rw [terminal18_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal18_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal18_side_norm)

/-- Archived far15 terminal row 19; closed chart interval [97/7936, 1/64]. -/
private theorem terminal19_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (97/7936 : ℝ) ≤ t) (hthi : t ≤ (1/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal19CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal19CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · right; right; right; left
      constructor <;> norm_num [terminal19CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal19CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal19CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal19CoreField, fieldScaleRat]

private theorem terminal19_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal19CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal19CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal19_core_orbit :
    terminal19CoreField = coreOrbitVertices
      (terminal19CoreField[0]'(by decide))
      (terminal19CoreField[1]'(by decide)) := by
  norm_num [terminal19CoreField, coreOrbitVertices, rotateQ]

theorem terminal19_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (97/7936 : ℝ) ≤ t) (hthi : t ≤ (1/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal19CoreField.map qpointFieldNormalize)) q := by
  rw [terminal19_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal19_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal19_side_norm)

end
end ElevenSquare.Tasks.T07
