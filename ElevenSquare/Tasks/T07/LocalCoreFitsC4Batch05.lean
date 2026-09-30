import ElevenSquare.Tasks.T07.LocalCoreFitsC4
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch05
import Mathlib.Tactic.NormNum

/-! Compact terminal CoreFits proofs generated from far15y-self-300.json.
Source SHA-256: 3903f42192cfb17b18675d59378379ae9b83ca540d41cc14482565fe32c73abe.
The Python emitter is untrusted; every inequality is kernel-checked by Lean. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal row 230; closed chart interval [243/256, 61/64]. -/
private theorem terminal230_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (243/256 : ℝ) ≤ t) (hthi : t ≤ (61/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal230CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal230CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal230CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal230CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal230CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal230CoreField, fieldScaleRat]

private theorem terminal230_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal230CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal230CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal230_core_orbit :
    terminal230CoreField = coreOrbitVertices
      (terminal230CoreField[0]'(by decide))
      (terminal230CoreField[1]'(by decide)) := by
  norm_num [terminal230CoreField, coreOrbitVertices, rotateQ]

theorem terminal230_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (243/256 : ℝ) ≤ t) (hthi : t ≤ (61/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal230CoreField.map qpointFieldNormalize)) q := by
  rw [terminal230_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal230_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal230_side_norm)

/-- Archived far15 terminal row 231; closed chart interval [61/64, 245/256]. -/
private theorem terminal231_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (61/64 : ℝ) ≤ t) (hthi : t ≤ (245/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal231CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal231CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal231CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal231CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal231CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal231CoreField, fieldScaleRat]

private theorem terminal231_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal231CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal231CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal231_core_orbit :
    terminal231CoreField = coreOrbitVertices
      (terminal231CoreField[0]'(by decide))
      (terminal231CoreField[1]'(by decide)) := by
  norm_num [terminal231CoreField, coreOrbitVertices, rotateQ]

theorem terminal231_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (61/64 : ℝ) ≤ t) (hthi : t ≤ (245/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal231CoreField.map qpointFieldNormalize)) q := by
  rw [terminal231_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal231_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal231_side_norm)

/-- Archived far15 terminal row 232; closed chart interval [245/256, 123/128]. -/
private theorem terminal232_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (245/256 : ℝ) ≤ t) (hthi : t ≤ (123/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal232CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal232CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal232CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal232CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal232CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal232CoreField, fieldScaleRat]

private theorem terminal232_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal232CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal232CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal232_core_orbit :
    terminal232CoreField = coreOrbitVertices
      (terminal232CoreField[0]'(by decide))
      (terminal232CoreField[1]'(by decide)) := by
  norm_num [terminal232CoreField, coreOrbitVertices, rotateQ]

theorem terminal232_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (245/256 : ℝ) ≤ t) (hthi : t ≤ (123/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal232CoreField.map qpointFieldNormalize)) q := by
  rw [terminal232_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal232_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal232_side_norm)

/-- Archived far15 terminal row 233; closed chart interval [123/128, 247/256]. -/
private theorem terminal233_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (123/128 : ℝ) ≤ t) (hthi : t ≤ (247/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal233CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal233CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal233CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal233CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal233CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal233CoreField, fieldScaleRat]

private theorem terminal233_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal233CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal233CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal233_core_orbit :
    terminal233CoreField = coreOrbitVertices
      (terminal233CoreField[0]'(by decide))
      (terminal233CoreField[1]'(by decide)) := by
  norm_num [terminal233CoreField, coreOrbitVertices, rotateQ]

theorem terminal233_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (123/128 : ℝ) ≤ t) (hthi : t ≤ (247/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal233CoreField.map qpointFieldNormalize)) q := by
  rw [terminal233_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal233_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal233_side_norm)

/-- Archived far15 terminal row 234; closed chart interval [247/256, 31/32]. -/
private theorem terminal234_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (247/256 : ℝ) ≤ t) (hthi : t ≤ (31/32 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal234CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal234CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal234CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal234CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal234CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal234CoreField, fieldScaleRat]

private theorem terminal234_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal234CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal234CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal234_core_orbit :
    terminal234CoreField = coreOrbitVertices
      (terminal234CoreField[0]'(by decide))
      (terminal234CoreField[1]'(by decide)) := by
  norm_num [terminal234CoreField, coreOrbitVertices, rotateQ]

theorem terminal234_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (247/256 : ℝ) ≤ t) (hthi : t ≤ (31/32 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal234CoreField.map qpointFieldNormalize)) q := by
  rw [terminal234_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal234_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal234_side_norm)

/-- Archived far15 terminal row 235; closed chart interval [31/32, 249/256]. -/
private theorem terminal235_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (31/32 : ℝ) ≤ t) (hthi : t ≤ (249/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal235CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal235CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal235CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal235CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal235CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal235CoreField, fieldScaleRat]

private theorem terminal235_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal235CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal235CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal235_core_orbit :
    terminal235CoreField = coreOrbitVertices
      (terminal235CoreField[0]'(by decide))
      (terminal235CoreField[1]'(by decide)) := by
  norm_num [terminal235CoreField, coreOrbitVertices, rotateQ]

theorem terminal235_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (31/32 : ℝ) ≤ t) (hthi : t ≤ (249/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal235CoreField.map qpointFieldNormalize)) q := by
  rw [terminal235_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal235_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal235_side_norm)

/-- Archived far15 terminal row 236; closed chart interval [249/256, 125/128]. -/
private theorem terminal236_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (249/256 : ℝ) ≤ t) (hthi : t ≤ (125/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal236CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal236CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal236CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal236CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal236CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal236CoreField, fieldScaleRat]

private theorem terminal236_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal236CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal236CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal236_core_orbit :
    terminal236CoreField = coreOrbitVertices
      (terminal236CoreField[0]'(by decide))
      (terminal236CoreField[1]'(by decide)) := by
  norm_num [terminal236CoreField, coreOrbitVertices, rotateQ]

theorem terminal236_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (249/256 : ℝ) ≤ t) (hthi : t ≤ (125/128 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal236CoreField.map qpointFieldNormalize)) q := by
  rw [terminal236_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal236_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal236_side_norm)

/-- Archived far15 terminal row 237; closed chart interval [125/128, 251/256]. -/
private theorem terminal237_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (125/128 : ℝ) ≤ t) (hthi : t ≤ (251/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal237CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal237CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal237CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal237CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal237CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal237CoreField, fieldScaleRat]

private theorem terminal237_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal237CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal237CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal237_core_orbit :
    terminal237CoreField = coreOrbitVertices
      (terminal237CoreField[0]'(by decide))
      (terminal237CoreField[1]'(by decide)) := by
  norm_num [terminal237CoreField, coreOrbitVertices, rotateQ]

theorem terminal237_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (125/128 : ℝ) ≤ t) (hthi : t ≤ (251/256 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal237CoreField.map qpointFieldNormalize)) q := by
  rw [terminal237_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal237_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal237_side_norm)

/-- Archived far15 terminal row 238; closed chart interval [251/256, 63/64]. -/
private theorem terminal238_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (251/256 : ℝ) ≤ t) (hthi : t ≤ (63/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal238CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal238CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal238CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal238CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal238CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal238CoreField, fieldScaleRat]

private theorem terminal238_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal238CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal238CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal238_core_orbit :
    terminal238CoreField = coreOrbitVertices
      (terminal238CoreField[0]'(by decide))
      (terminal238CoreField[1]'(by decide)) := by
  norm_num [terminal238CoreField, coreOrbitVertices, rotateQ]

theorem terminal238_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (251/256 : ℝ) ≤ t) (hthi : t ≤ (63/64 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal238CoreField.map qpointFieldNormalize)) q := by
  rw [terminal238_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal238_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal238_side_norm)

/-- Archived far15 terminal row 239; closed chart interval [63/64, 125613/127232]. -/
private theorem terminal239_corner_open (q : UnitSquare) (t : ℝ)
    (htlo : (63/64 : ℝ) ≤ t) (hthi : t ≤ (125613/127232 : ℝ))
    (haxis : q.axis = chartAxis t) :
    OpenSquare q
      (q.center + realPoint (qpointFieldNormalize (terminal239CoreField[0]'(by decide)))) := by
  apply fieldCoreVertex_open_of_signed_quads q _ t haxis
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal239CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · right; left
      constructor <;> norm_num [terminal239CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · left
      constructor <;> norm_num [terminal239CoreField, fieldScaleRat]
  · unfold signedCoreQuad
    apply quadratic_pos_on_Icc
    · exact htlo
    · exact hthi
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · norm_num [Quadratic, terminal239CoreField, fieldScaleRat]
    · right; right; left
      constructor <;> norm_num [terminal239CoreField, fieldScaleRat]

private theorem terminal239_side_norm :
    normSq (realPoint (qpointFieldNormalize (terminal239CoreField[1]'(by decide)))) < 1/4 := by
  norm_num [terminal239CoreField, qpointFieldNormalize, realPoint,
    normSq, dot, fieldScaleRat]

private theorem terminal239_core_orbit :
    terminal239CoreField = coreOrbitVertices
      (terminal239CoreField[0]'(by decide))
      (terminal239CoreField[1]'(by decide)) := by
  norm_num [terminal239CoreField, coreOrbitVertices, rotateQ]

theorem terminal239_coreFits_c4 (q : UnitSquare) (t : ℝ)
    (htlo : (63/64 : ℝ) ≤ t) (hthi : t ≤ (125613/127232 : ℝ))
    (haxis : q.axis = chartAxis t) :
    CoreFits (rationalHull (terminal239CoreField.map qpointFieldNormalize)) q := by
  rw [terminal239_core_orbit]
  exact coreOrbit_coreFits q _ _
    (terminal239_corner_open q t htlo hthi haxis)
    (normalized_core_open_of_normSq_lt q _ terminal239_side_norm)

end
end ElevenSquare.Tasks.T07
