import ElevenSquare.Tasks.T03.UniversalCollision
import ElevenSquare.Tasks.T03.HullLinearCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

/-- Check the vertices of two closed hulls against a difference polygon.
Convexity extends this finite check to every pair of centers. -/
def differencePlaneCheck (xs ys : List QPoint) (ls : List IntegerPlane) : Bool :=
  decide (∀ x ∈ xs, ∀ y ∈ ys, ∀ l ∈ ls, l.pointCheck (x-y) = true)

theorem differencePlaneCheck_sound (xs ys : List QPoint) (ls : List IntegerPlane)
    (h : differencePlaneCheck xs ys ls = true) :
    ∀ x ∈ rationalHull xs, ∀ y ∈ rationalHull ys, x-y ∈ IntegerCarrier ls := by
  apply hull_difference_mem xs ys (IntegerCarrier ls)
  · rw [integerCarrier_as_polygon]
    exact polygon_convex _
  · intro x hx y hy l hl
    have hp := l.pointCheck_sound (x-y) ((of_decide_eq_true h) x hx y hy l hl)
    simpa [realPoint] using hp

theorem collision_of_difference_planes (xs ys qi qj : List QPoint)
    (ls : List IntegerPlane) (h : differencePlaneCheck xs ys ls = true)
    (hpoly : IntegerCarrier ls ⊆ forbiddenCenters (rationalHull qj) (rationalHull qi))
    (q r : UnitSquare) (hi : CoreFits (rationalHull qi) q)
    (hj : CoreFits (rationalHull qj) r)
    (hx : q.center ∈ rationalHull xs) (hy : r.center ∈ rationalHull ys) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p :=
  core_difference_overlap q r _ _ hi hj
    (hpoly (differencePlaneCheck_sound xs ys ls h q.center hx r.center hy))

end
end ElevenSquare.Pending.T03
