import ElevenSquare.Tasks.T07.NearSourceData0
import ElevenSquare.Tasks.T07.NearSourceData1
import ElevenSquare.Tasks.T07.NearSourceData2
import ElevenSquare.Tasks.T07.NearSourceData3
import ElevenSquare.Tasks.T07.NearSourceData4
import ElevenSquare.Tasks.T07.NearSourceData5
import ElevenSquare.Tasks.T07.NearSourceData6
import ElevenSquare.Tasks.T07.NearSourceData7
import ElevenSquare.Tasks.T07.NearSourceData8
import ElevenSquare.Tasks.T07.NearSourceData9
import ElevenSquare.Tasks.T07.NearSourceData10
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The frozen final pose domain. Coverage of a packing by these domains is an
explicit antecedent: this file checks the finite geometry of the final domains,
without claiming to replay the earlier outer-induction ancestry. -/
namespace ElevenSquare.Tasks.T07

def nearRows (i : Fin 11) : List NearPoseRow :=
  ![nearRows0, nearRows1, nearRows2, nearRows3, nearRows4, nearRows5,
    nearRows6, nearRows7, nearRows8, nearRows9, nearRows10] i

def nearFieldBox (i : Fin 11) : NearRatRect :=
  ![nearBox0, nearBox1, nearBox2, nearBox3, nearBox4, nearBox5,
    nearBox6, nearBox7, nearBox8, nearBox9, nearBox10] i

def nearAxis (i : Fin 11) : Bool := decide (i.val < 6)

theorem nearRows_valid (i : Fin 11) :
    List.Forall (NearPoseRow.Valid (nearFieldBox i) (nearAxis i)) (nearRows i) := by
  fin_cases i
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows0_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows1_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows2_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows3_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows4_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows5_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows6_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows7_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows8_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows9_valid
  · simpa [nearRows, nearFieldBox, nearAxis] using nearRows10_valid

def nearCastPoint (p : ℚ × ℚ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

def nearPolygon (P : List (ℚ × ℚ)) : Set (ℝ × ℝ) :=
  {p | ∃ q ∈ P, nearCastPoint q = p}

def InFinalNearCenter (i : Fin 11) (p : ℝ × ℝ) : Prop :=
  ∃ r ∈ nearRows i, ∃ P ∈ r.polygons, p ∈ convexHull ℝ (nearPolygon P)

theorem nearRatRect_cast {b : NearRatRect} {q : ℚ × ℚ}
    (hq : b.Contains q) :
    inRect (b.lx : ℝ) (b.hx : ℝ) (b.ly : ℝ) (b.hy : ℝ) (nearCastPoint q) := by
  change (b.lx : ℝ) ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ (b.hx : ℝ) ∧
    (b.ly : ℝ) ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ (b.hy : ℝ)
  rcases hq with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by exact_mod_cast hxl, by exact_mod_cast hxu,
    by exact_mod_cast hyl, by exact_mod_cast hyu⟩

theorem finalNear_center_field_enclosure (i : Fin 11) (p : ℝ × ℝ)
    (hp : InFinalNearCenter i p) :
    inRect ((nearFieldBox i).lx : ℝ) ((nearFieldBox i).hx : ℝ)
      ((nearFieldBox i).ly : ℝ) ((nearFieldBox i).hy : ℝ) p := by
  obtain ⟨r, hr, P, hP, hpP⟩ := hp
  have hvalid := (List.forall_iff_forall_mem.mp (nearRows_valid i)) r hr
  obtain ⟨_, _, _, _, hpolys⟩ := hvalid
  obtain ⟨_, hpoints⟩ := (List.forall_iff_forall_mem.mp hpolys) P hP
  apply hull_in_rect (v := nearPolygon P) ?_ p hpP
  intro q hq
  obtain ⟨a, ha, rfl⟩ := hq
  exact nearRatRect_cast ((List.forall_iff_forall_mem.mp hpoints) a ha)

end ElevenSquare.Tasks.T07
