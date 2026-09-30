import ElevenSquare.Tasks.T03.HomogeneousPoints
import ElevenSquare.Tasks.T03.DifferenceSupport

namespace ElevenSquare.Pending.T03
noncomputable section

def homHullFastCheck (ps : List HomPoint) (ls : List IntegerPlane) : Bool :=
  ps.all (fun p => ls.all p.planeCheck)

theorem homHullFastCheck_sound (ps : List HomPoint) (ls : List IntegerPlane)
    (h : homHullFastCheck ps ls = true) : rationalHull (ps.map HomPoint.point) ⊆ IntegerCarrier ls := by
  simp only [homHullFastCheck,List.all_eq_true] at h
  exact homHullCheck_sound ps ls (decide_eq_true h)

def DifferenceSupport.homCheck (w : DifferenceSupport) (l : IntegerPlane)
    (xs ys : List HomPoint) : Bool :=
  decide (0 < w.denominator) && homHullFastCheck xs [w.left l] && homHullFastCheck ys [w.right l]

theorem DifferenceSupport.homSound (w : DifferenceSupport) (l : IntegerPlane)
    (xs ys : List HomPoint) (h : w.homCheck l xs ys = true)
    (x : Point) (hx : x ∈ rationalHull (xs.map HomPoint.point))
    (y : Point) (hy : y ∈ rationalHull (ys.map HomPoint.point)) : l.holds (x-y) := by
  simp only [DifferenceSupport.homCheck,Bool.and_eq_true] at h
  have hd : (0:ℝ) < w.denominator := by exact_mod_cast of_decide_eq_true h.1.1
  have hl := homHullFastCheck_sound xs [w.left l] h.1.2 hx (w.left l) (by simp)
  have hr := homHullFastCheck_sound ys [w.right l] h.2 hy (w.right l) (by simp)
  dsimp [IntegerPlane.holds,DifferenceSupport.left,DifferenceSupport.right] at hl hr ⊢
  push_cast at hl hr
  apply (mul_le_mul_left hd).mp
  nlinarith only [hl,hr]

def homSupportCheck (xs ys : List HomPoint) : List IntegerPlane → List DifferenceSupport → Bool
  | [], [] => true
  | l::ls,w::ws => w.homCheck l xs ys && homSupportCheck xs ys ls ws
  | _, _ => false

theorem homSupportCheck_sound (xs ys : List HomPoint) (ls : List IntegerPlane)
    (ws : List DifferenceSupport) (h : homSupportCheck xs ys ls ws = true)
    (x : Point) (hx : x ∈ rationalHull (xs.map HomPoint.point))
    (y : Point) (hy : y ∈ rationalHull (ys.map HomPoint.point)) : x-y ∈ IntegerCarrier ls := by
  induction ls generalizing ws with
  | nil => intro l hl; cases hl
  | cons l ls ih =>
    cases ws with
    | nil => simp [homSupportCheck] at h
    | cons w ws =>
      simp only [homSupportCheck,Bool.and_eq_true] at h
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact w.homSound k xs ys h.1 x hx y hy
      · exact ih ws h.2 k hk

end
end ElevenSquare.Pending.T03
