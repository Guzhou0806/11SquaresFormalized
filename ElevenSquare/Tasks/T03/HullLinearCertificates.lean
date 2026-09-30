import ElevenSquare.Tasks.T03.CellLinear
import ElevenSquare.Tasks.T03.LinearCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def IntegerPlane.pointCheck (l : IntegerPlane) (p : QPoint) : Bool :=
  decide ((l.a:ℚ)*p.1+(l.b:ℚ)*p.2 ≤ (l.c:ℚ))

theorem IntegerPlane.pointCheck_sound (l : IntegerPlane) (p : QPoint)
    (h : l.pointCheck p = true) : l.holds (realPoint p) := by
  have hp := of_decide_eq_true h
  dsimp [IntegerPlane.holds,realPoint]
  exact_mod_cast hp

def hullLinearCheck (vs : List QPoint) (ls : List IntegerPlane) : Bool :=
  decide (∀ v ∈ vs, ∀ l ∈ ls, l.pointCheck v = true)

theorem hullLinearCheck_sound (vs : List QPoint) (ls : List IntegerPlane)
    (h : hullLinearCheck vs ls = true) : rationalHull vs ⊆ IntegerCarrier ls := by
  rw [integerCarrier_as_polygon]
  apply rationalHull_in_polygon
  intro v hv l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  exact (k.rational_correct (realPoint v)).mpr (k.pointCheck_sound v ((of_decide_eq_true h) v hv k hk))

end
end ElevenSquare.Pending.T03
