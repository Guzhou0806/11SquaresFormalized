import ElevenSquare.Tasks.T03.CollisionPlanes

namespace ElevenSquare.Pending.T03
noncomputable section

/-- Coordinates with a common positive denominator permit integer-only checks.
Positivity is checked explicitly, and the geometric point is still rational. -/
structure HomPoint where
  x : ℤ
  y : ℤ
  denominator : ℕ

def HomPoint.point (p : HomPoint) : QPoint :=
  ((p.x:ℚ)/p.denominator,(p.y:ℚ)/p.denominator)

def HomPoint.planeCheck (p : HomPoint) (l : IntegerPlane) : Bool :=
  decide (0 < p.denominator ∧ l.a*p.x+l.b*p.y ≤ l.c*p.denominator)

theorem HomPoint.planeCheck_sound (p : HomPoint) (l : IntegerPlane)
    (h : p.planeCheck l = true) : l.holds (realPoint p.point) := by
  obtain ⟨hd,hp⟩ := of_decide_eq_true h
  have hd' : (0:ℝ) < p.denominator := by exact_mod_cast hd
  have hp' : (l.a:ℝ)*p.x+(l.b:ℝ)*p.y ≤ (l.c:ℝ)*p.denominator := by exact_mod_cast hp
  dsimp [IntegerPlane.holds,realPoint,HomPoint.point]
  push_cast
  calc
    (l.a:ℝ)*((p.x:ℝ)/p.denominator)+(l.b:ℝ)*((p.y:ℝ)/p.denominator) =
        ((l.a:ℝ)*p.x+(l.b:ℝ)*p.y)/p.denominator := by ring
    _ ≤ (l.c:ℝ) := (div_le_iff hd').mpr hp'

def HomPoint.sub (p q : HomPoint) : HomPoint :=
  ⟨p.x*q.denominator-q.x*p.denominator,p.y*q.denominator-q.y*p.denominator,
    p.denominator*q.denominator⟩

theorem HomPoint.sub_point (p q : HomPoint) (hp : 0 < p.denominator) (hq : 0 < q.denominator) :
    (p.sub q).point = p.point-q.point := by
  have hp' : (p.denominator:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hq' : (q.denominator:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  ext <;> dsimp [HomPoint.point,HomPoint.sub] <;> push_cast <;>
    field_simp [hp',hq'] <;> ring

def homHullCheck (ps : List HomPoint) (ls : List IntegerPlane) : Bool :=
  decide (∀ p ∈ ps, ∀ l ∈ ls, p.planeCheck l = true)

theorem homHullCheck_sound (ps : List HomPoint) (ls : List IntegerPlane)
    (h : homHullCheck ps ls = true) : rationalHull (ps.map HomPoint.point) ⊆ IntegerCarrier ls := by
  rw [integerCarrier_as_polygon]
  apply rationalHull_in_polygon
  intro v hv l hl
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  exact (k.rational_correct _).mpr (p.planeCheck_sound k ((of_decide_eq_true h) p hp k hk))

def homDifferenceCheck (xs ys : List HomPoint) (ls : List IntegerPlane) : Bool :=
  decide ((∀ x ∈ xs, 0 < x.denominator) ∧ (∀ y ∈ ys, 0 < y.denominator) ∧
    ∀ x ∈ xs, ∀ y ∈ ys, ∀ l ∈ ls, (x.sub y).planeCheck l = true)

theorem homDifferenceCheck_sound (xs ys : List HomPoint) (ls : List IntegerPlane)
    (h : homDifferenceCheck xs ys ls = true) :
    ∀ x ∈ rationalHull (xs.map HomPoint.point), ∀ y ∈ rationalHull (ys.map HomPoint.point),
      x-y ∈ IntegerCarrier ls := by
  obtain ⟨hxpos,hypos,hcheck⟩ := of_decide_eq_true h
  apply hull_difference_mem (xs.map HomPoint.point) (ys.map HomPoint.point) (IntegerCarrier ls)
  · rw [integerCarrier_as_polygon]; exact polygon_convex _
  · intro x hx y hy l hl
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    have hh := (a.sub b).planeCheck_sound l (hcheck a ha b hb l hl)
    rw [HomPoint.sub_point a b (hxpos a ha) (hypos b hb)] at hh
    simpa [realPoint] using hh

end
end ElevenSquare.Pending.T03
