import ElevenSquare.Tasks.T03.CollisionPlanes

namespace ElevenSquare.Pending.T03
noncomputable section

/-- One separating support value avoids checking every pair of vertices. -/
structure DifferenceSupport where
  numerator : ℤ
  denominator : ℕ

def DifferenceSupport.left (w : DifferenceSupport) (l : IntegerPlane) : IntegerPlane :=
  ⟨w.denominator*l.a,w.denominator*l.b,w.numerator⟩

def DifferenceSupport.right (w : DifferenceSupport) (l : IntegerPlane) : IntegerPlane :=
  ⟨-(w.denominator*l.a),-(w.denominator*l.b),w.denominator*l.c-w.numerator⟩

def DifferenceSupport.check (w : DifferenceSupport) (l : IntegerPlane)
    (xs ys : List QPoint) : Bool :=
  decide (0 < w.denominator) && hullLinearCheck xs [w.left l] && hullLinearCheck ys [w.right l]

theorem DifferenceSupport.sound (w : DifferenceSupport) (l : IntegerPlane)
    (xs ys : List QPoint) (h : w.check l xs ys = true)
    (x : Point) (hx : x ∈ rationalHull xs) (y : Point) (hy : y ∈ rationalHull ys) :
    l.holds (x-y) := by
  simp only [DifferenceSupport.check,Bool.and_eq_true] at h
  have hd : (0:ℝ) < w.denominator := by exact_mod_cast of_decide_eq_true h.1.1
  have hl := hullLinearCheck_sound xs [w.left l] h.1.2 hx (w.left l) (by simp)
  have hr := hullLinearCheck_sound ys [w.right l] h.2 hy (w.right l) (by simp)
  dsimp [IntegerPlane.holds,DifferenceSupport.left,DifferenceSupport.right] at hl hr ⊢
  push_cast at hl hr
  apply (mul_le_mul_left hd).mp
  nlinarith only [hl,hr]

def differenceSupportCheck (xs ys : List QPoint) :
    List IntegerPlane → List DifferenceSupport → Bool
  | [], [] => true
  | l::ls, w::ws => w.check l xs ys && differenceSupportCheck xs ys ls ws
  | _, _ => false

theorem differenceSupportCheck_sound (xs ys : List QPoint) (ls : List IntegerPlane)
    (ws : List DifferenceSupport) (h : differenceSupportCheck xs ys ls ws = true)
    (x : Point) (hx : x ∈ rationalHull xs) (y : Point) (hy : y ∈ rationalHull ys) :
    x-y ∈ IntegerCarrier ls := by
  induction ls generalizing ws with
  | nil => intro l hl; cases hl
  | cons l ls ih =>
    cases ws with
    | nil => simp [differenceSupportCheck] at h
    | cons w ws =>
      simp only [differenceSupportCheck,Bool.and_eq_true] at h
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact w.sound k xs ys h.1 x hx y hy
      · exact ih ws h.2 k hk

theorem collision_of_difference_supports (xs ys qi qj : List QPoint)
    (ls : List IntegerPlane) (ws : List DifferenceSupport)
    (h : differenceSupportCheck xs ys ls ws = true)
    (hpoly : IntegerCarrier ls ⊆ forbiddenCenters (rationalHull qj) (rationalHull qi))
    (q r : UnitSquare) (hi : CoreFits (rationalHull qi) q)
    (hj : CoreFits (rationalHull qj) r)
    (hx : q.center ∈ rationalHull xs) (hy : r.center ∈ rationalHull ys) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p :=
  core_difference_overlap q r _ _ hi hj
    (hpoly (differenceSupportCheck_sound xs ys ls ws h q.center hx r.center hy))

end
end ElevenSquare.Pending.T03
