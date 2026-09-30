import ElevenSquare.Pending.S07_SlabBounds
import ElevenSquare.Pending.S07_IntegerOverlay
namespace ElevenSquare.Pending

-- An edge point belongs to a convex set whenever its x-coordinate lies between
-- two points of that set on a nonvertical supporting line.
theorem convex_point_on_edge {C : Set Point} (hc : Convex ℝ C)
    (A B D left right lo hi x y : ℝ) (hb : B ≠ 0)
    (hw : left < right) (hx0 : left ≤ x) (hx1 : x ≤ right)
    (hlmem : (left,lo) ∈ C) (hrmem : (right,hi) ∈ C)
    (hl : A*left+B*lo=D) (hr : A*right+B*hi=D) (hp : A*x+B*y=D) :
    (x,y) ∈ C := by
  have he : (right-left)*y = (right-x)*lo+(x-left)*hi := by
    have hid := edge_interpolation_identity A B D left right lo hi x y hl hr
    rw [hp, sub_self, mul_zero] at hid
    have := (mul_eq_zero.mp hid).resolve_left hb
    linarith
  exact convex_trapezoid hc left right lo hi lo hi x y hw hlmem hrmem hlmem hrmem
    hx0 hx1 he.ge he.le

def FractionPoint.onPlaneCheck (q : FractionPoint) (l : IntegerPlane) : Bool :=
  decide (0 < q.dx ∧ 0 < q.dy ∧ l.a*q.nx*q.dy+l.b*q.ny*q.dx = l.c*q.dx*q.dy)

theorem FractionPoint.onPlaneCheck_sound (q : FractionPoint) (l : IntegerPlane)
    (h : q.onPlaneCheck l = true) :
    (l.a:ℝ)*(realPoint q.rational).1+(l.b:ℝ)*(realPoint q.rational).2=(l.c:ℝ) := by
  have hn := of_decide_eq_true h
  have hx : (q.dx:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn.1 : (0:ℝ) < q.dx)
  have hy : (q.dy:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn.2.1 : (0:ℝ) < q.dy)
  have hi : (l.a:ℝ)*(q.nx:ℝ)*(q.dy:ℝ)+(l.b:ℝ)*(q.ny:ℝ)*(q.dx:ℝ) =
      (l.c:ℝ)*(q.dx:ℝ)*(q.dy:ℝ) := by exact_mod_cast hn.2.2
  dsimp [realPoint, FractionPoint.rational]
  push_cast
  field_simp [hx,hy]
  nlinarith [hi]

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.convex_point_on_edge
#print axioms ElevenSquare.Pending.FractionPoint.onPlaneCheck_sound
