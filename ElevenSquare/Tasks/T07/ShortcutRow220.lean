import ElevenSquare.Tasks.T07.ShortcutFieldCollision
import ElevenSquare.Tasks.T07.Far15Row220
import Mathlib.Tactic.NormNum

/-! One complete archived source row through the generic collision checker.
The source's seven field vertices and whole closed angular interval are used;
the point is converted to the physical unit-square frame. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem far15_row220_bernstein_vertices :
    ∀ v ∈ far15Row220Vertices,
      FieldCollisionCert fieldScale (realPoint v)
        (realPoint far15Owner9Witness) (233/256 : ℝ) (117/128 : ℝ) := by
  intro v hv
  simp only [far15Row220Vertices, List.mem_cons, List.not_mem_nil,
    or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [FieldCollisionCert, QuadraticIntervalCert,
    quadraticAt, quadraticBernsteinMiddle, fieldDX, fieldDY,
    realPoint, far15Owner9Witness, fieldScale, coverCap]

theorem far15_row220_bernstein_collision (q : UnitSquare)
    (hc : toField q.center ∈ rationalHull far15Row220Vertices)
    (ht : ∃ t : ℝ, (233/256 : ℝ) ≤ t ∧ t ≤ 117/128 ∧
      q.axis = chartAxis t) :
    OpenSquare q
      ((far15Owner9Witness.1 : ℝ)/fieldScale,
       (far15Owner9Witness.2 : ℝ)/fieldScale) := by
  have ht' : ∃ t : ℝ,
      (((233/256 : ℚ) : ℝ)) ≤ t ∧ t ≤ (((117/128 : ℚ) : ℝ)) ∧
      q.axis = chartAxis t := by
    simpa using ht
  have hv' : ∀ v ∈ far15Row220Vertices,
      FieldCollisionCert fieldScale (realPoint v)
        (realPoint far15Owner9Witness)
        (((233/256 : ℚ) : ℝ)) (((117/128 : ℚ) : ℝ)) := by
    intro v hv
    simpa using far15_row220_bernstein_vertices v hv
  exact fieldHull_collision q far15Row220Vertices far15Owner9Witness
    (233/256 : ℚ) (117/128 : ℚ) hc ht' (by norm_num)
    hv'

end
end ElevenSquare.Tasks.T07
