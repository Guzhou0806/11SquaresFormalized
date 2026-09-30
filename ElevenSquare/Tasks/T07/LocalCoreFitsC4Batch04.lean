import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch04
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 220; closed chart interval [233/256, 117/128]. -/
private theorem terminal220_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (233/256 : ℝ) ≤ t) (hthi : t ≤ (117/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal220CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal220CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal220CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal220CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal220CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal220CoreField, fieldScaleRat]

private theorem terminal220_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal220CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal220CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal220_core_orbit :
    terminal220CoreField = coreOrbitVertices
      (terminal220CoreField[0]'(by decide))
      (terminal220CoreField[1]'(by decide)) := by
  norm_num [terminal220CoreField, coreOrbitVertices, rotateQ]

theorem terminal220_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (233/256 : ℝ) ≤ t) (hthi : t ≤ (117/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal220CoreField.map qpointFieldNormalize)) q := by
  rw [terminal220_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal220_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal220_side_norm)

/-- Archived far15 terminal row 221; closed chart interval [117/128, 235/256]. -/
private theorem terminal221_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (117/128 : ℝ) ≤ t) (hthi : t ≤ (235/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal221CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal221CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal221CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal221CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal221CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal221CoreField, fieldScaleRat]

private theorem terminal221_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal221CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal221CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal221_core_orbit :
    terminal221CoreField = coreOrbitVertices
      (terminal221CoreField[0]'(by decide))
      (terminal221CoreField[1]'(by decide)) := by
  norm_num [terminal221CoreField, coreOrbitVertices, rotateQ]

theorem terminal221_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (117/128 : ℝ) ≤ t) (hthi : t ≤ (235/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal221CoreField.map qpointFieldNormalize)) q := by
  rw [terminal221_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal221_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal221_side_norm)

/-- Archived far15 terminal row 222; closed chart interval [235/256, 59/64]. -/
private theorem terminal222_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (235/256 : ℝ) ≤ t) (hthi : t ≤ (59/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal222CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal222CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal222CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal222CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal222CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal222CoreField, fieldScaleRat]

private theorem terminal222_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal222CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal222CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal222_core_orbit :
    terminal222CoreField = coreOrbitVertices
      (terminal222CoreField[0]'(by decide))
      (terminal222CoreField[1]'(by decide)) := by
  norm_num [terminal222CoreField, coreOrbitVertices, rotateQ]

theorem terminal222_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (235/256 : ℝ) ≤ t) (hthi : t ≤ (59/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal222CoreField.map qpointFieldNormalize)) q := by
  rw [terminal222_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal222_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal222_side_norm)

/-- Archived far15 terminal row 223; closed chart interval [59/64, 237/256]. -/
private theorem terminal223_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (59/64 : ℝ) ≤ t) (hthi : t ≤ (237/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal223CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal223CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal223CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal223CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal223CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal223CoreField, fieldScaleRat]

private theorem terminal223_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal223CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal223CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal223_core_orbit :
    terminal223CoreField = coreOrbitVertices
      (terminal223CoreField[0]'(by decide))
      (terminal223CoreField[1]'(by decide)) := by
  norm_num [terminal223CoreField, coreOrbitVertices, rotateQ]

theorem terminal223_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (59/64 : ℝ) ≤ t) (hthi : t ≤ (237/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal223CoreField.map qpointFieldNormalize)) q := by
  rw [terminal223_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal223_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal223_side_norm)

/-- Archived far15 terminal row 224; closed chart interval [237/256, 119/128]. -/
private theorem terminal224_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (237/256 : ℝ) ≤ t) (hthi : t ≤ (119/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal224CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal224CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal224CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal224CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal224CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal224CoreField, fieldScaleRat]

private theorem terminal224_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal224CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal224CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal224_core_orbit :
    terminal224CoreField = coreOrbitVertices
      (terminal224CoreField[0]'(by decide))
      (terminal224CoreField[1]'(by decide)) := by
  norm_num [terminal224CoreField, coreOrbitVertices, rotateQ]

theorem terminal224_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (237/256 : ℝ) ≤ t) (hthi : t ≤ (119/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal224CoreField.map qpointFieldNormalize)) q := by
  rw [terminal224_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal224_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal224_side_norm)

/-- Archived far15 terminal row 225; closed chart interval [119/128, 239/256]. -/
private theorem terminal225_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (119/128 : ℝ) ≤ t) (hthi : t ≤ (239/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal225CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal225CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal225CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal225CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal225CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal225CoreField, fieldScaleRat]

private theorem terminal225_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal225CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal225CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal225_core_orbit :
    terminal225CoreField = coreOrbitVertices
      (terminal225CoreField[0]'(by decide))
      (terminal225CoreField[1]'(by decide)) := by
  norm_num [terminal225CoreField, coreOrbitVertices, rotateQ]

theorem terminal225_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (119/128 : ℝ) ≤ t) (hthi : t ≤ (239/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal225CoreField.map qpointFieldNormalize)) q := by
  rw [terminal225_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal225_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal225_side_norm)

/-- Archived far15 terminal row 226; closed chart interval [239/256, 15/16]. -/
private theorem terminal226_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (239/256 : ℝ) ≤ t) (hthi : t ≤ (15/16 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal226CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal226CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal226CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal226CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal226CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal226CoreField, fieldScaleRat]

private theorem terminal226_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal226CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal226CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal226_core_orbit :
    terminal226CoreField = coreOrbitVertices
      (terminal226CoreField[0]'(by decide))
      (terminal226CoreField[1]'(by decide)) := by
  norm_num [terminal226CoreField, coreOrbitVertices, rotateQ]

theorem terminal226_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (239/256 : ℝ) ≤ t) (hthi : t ≤ (15/16 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal226CoreField.map qpointFieldNormalize)) q := by
  rw [terminal226_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal226_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal226_side_norm)

/-- Archived far15 terminal row 227; closed chart interval [15/16, 241/256]. -/
private theorem terminal227_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (15/16 : ℝ) ≤ t) (hthi : t ≤ (241/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal227CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal227CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal227CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal227CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal227CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal227CoreField, fieldScaleRat]

private theorem terminal227_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal227CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal227CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal227_core_orbit :
    terminal227CoreField = coreOrbitVertices
      (terminal227CoreField[0]'(by decide))
      (terminal227CoreField[1]'(by decide)) := by
  norm_num [terminal227CoreField, coreOrbitVertices, rotateQ]

theorem terminal227_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (15/16 : ℝ) ≤ t) (hthi : t ≤ (241/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal227CoreField.map qpointFieldNormalize)) q := by
  rw [terminal227_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal227_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal227_side_norm)

/-- Archived far15 terminal row 228; closed chart interval [241/256, 121/128]. -/
private theorem terminal228_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (241/256 : ℝ) ≤ t) (hthi : t ≤ (121/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal228CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal228CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal228CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal228CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal228CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal228CoreField, fieldScaleRat]

private theorem terminal228_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal228CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal228CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal228_core_orbit :
    terminal228CoreField = coreOrbitVertices
      (terminal228CoreField[0]'(by decide))
      (terminal228CoreField[1]'(by decide)) := by
  norm_num [terminal228CoreField, coreOrbitVertices, rotateQ]

theorem terminal228_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (241/256 : ℝ) ≤ t) (hthi : t ≤ (121/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal228CoreField.map qpointFieldNormalize)) q := by
  rw [terminal228_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal228_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal228_side_norm)

/-- Archived far15 terminal row 229; closed chart interval [121/128, 243/256]. -/
private theorem terminal229_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (121/128 : ℝ) ≤ t) (hthi : t ≤ (243/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal229CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal229CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal229CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal229CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal229CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal229CoreField, fieldScaleRat]

private theorem terminal229_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal229CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal229CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal229_core_orbit :
    terminal229CoreField = coreOrbitVertices
      (terminal229CoreField[0]'(by decide))
      (terminal229CoreField[1]'(by decide)) := by
  norm_num [terminal229CoreField, coreOrbitVertices, rotateQ]

theorem terminal229_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (121/128 : ℝ) ≤ t) (hthi : t ≤ (243/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal229CoreField.map qpointFieldNormalize)) q := by
  rw [terminal229_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal229_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal229_side_norm)

end
end ElevenSquare.Tasks.T07
