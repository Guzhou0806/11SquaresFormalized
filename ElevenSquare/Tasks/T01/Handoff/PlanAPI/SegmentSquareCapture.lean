import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SegmentBox
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- Six support inequalities for a segment to meet a square-centered core
    of half-width `h`. The final condition is the perpendicular projection. -/
def SegmentSquareBounds (q : UnitSquare) (A B : Point) (h : ℝ) : Prop :=
  min (localX q A) (localX q B) ≤ h ∧
  -h ≤ max (localX q A) (localX q B) ∧
  min (localY q A) (localY q B) ≤ h ∧
  -h ≤ max (localY q A) (localY q B) ∧
  |localX q A * (localY q B - localY q A) -
    localY q A * (localX q B - localX q A)| ≤
    h * (|localX q B - localX q A| + |localY q B - localY q A|)

/-- A segment satisfying the six support bounds for a strict inner core
    contains a point in the open unit square. -/
theorem segment_square_capture (q : UnitSquare) (A B : Point) (h : ℝ)
    (hh : 0 ≤ h) (hstrict : h < 1 / 2)
    (hb : SegmentSquareBounds q A B h) :
    ∃ p ∈ convexHull ℝ ({A, B} : Set Point), OpenSquare q p := by
  rcases hb with ⟨hxmin, hxmax, hymin, hymax, hcross⟩
  obtain ⟨t, ht0, ht1, hxl, hxu, hyl, hyu⟩ :=
    segment_hits_closed_square (localX q A) (localY q A)
      (localX q B - localX q A) (localY q B - localY q A) h hh
      (by convert hxmin using 1 <;> ring)
      (by convert hxmax using 1 <;> ring)
      (by convert hymin using 1 <;> ring)
      (by convert hymax using 1 <;> ring) hcross
  let p : Point := (1 - t) • A + t • B
  have hseg : p ∈ segment ℝ A B := by
    rw [segment_eq_image]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hp : p ∈ convexHull ℝ ({A, B} : Set Point) := by
    simpa only [convexHull_pair] using hseg
  have hX : localX q p = localX q A + t * (localX q B - localX q A) := by
    dsimp [p, localX, dot]
    ring
  have hY : localY q p = localY q A + t * (localY q B - localY q A) := by
    dsimp [p, localY, perp, dot]
    ring
  refine ⟨p, hp, ?_⟩
  unfold OpenSquare
  rw [abs_lt, abs_lt, hX, hY]
  constructor <;> constructor <;> linarith

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.segment_square_capture
