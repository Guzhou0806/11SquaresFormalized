import ElevenSquare.Pending.Types
import ElevenSquare.BasicGeometry

namespace ElevenSquare.Pending
noncomputable section

-- A scalar convexity argument; no finite certificate search or enumeration.
theorem squared_distance_on_hulls (A B : List QPoint) (d : ℝ)
    (hv : ∀ a ∈ A, ∀ b ∈ B, normSq (realPoint a-realPoint b) ≤ d) :
    ∀ p ∈ rationalHull A, ∀ q ∈ rationalHull B, normSq (p-q) ≤ d := by
  have swap (x y : Point) : normSq (x-y) = normSq (y-x) := by
    dsimp [normSq, dot]
    ring
  have ball_convex (z : Point) : Convex ℝ {p : Point | normSq (p-z) ≤ d} := by
    intro x hx y hy a b ha hb hab
    change normSq (x-z) ≤ d at hx
    change normSq (y-z) ≤ d at hy
    have hid : normSq ((a • x+b • y)-z) =
        a*normSq (x-z)+b*normSq (y-z)-a*b*normSq (x-y) := by
      have hb_eq : b = 1-a := by linarith only [hab]
      rw [hb_eq]
      dsimp [normSq, dot]
      ring
    change normSq ((a • x+b • y)-z) ≤ d
    rw [hid]
    have hx' := mul_le_mul_of_nonneg_left hx ha
    have hy' := mul_le_mul_of_nonneg_left hy hb
    calc
      a*normSq (x-z)+b*normSq (y-z)-a*b*normSq (x-y)
          ≤ a*normSq (x-z)+b*normSq (y-z) :=
        sub_le_self _ (mul_nonneg (mul_nonneg ha hb) (normSq_nonneg (x-y)))
      _ ≤ a*d+b*d := add_le_add hx' hy'
      _ = d := by rw [← add_mul, hab, one_mul]
  have left (b : QPoint) (hb : b ∈ B) :
      rationalHull A ⊆ {p : Point | normSq (p-realPoint b) ≤ d} := by
    apply convexHull_min _ (ball_convex (realPoint b))
    rintro p ⟨a, ha, rfl⟩
    exact hv a ha b hb
  intro p hp q hq
  have right : rationalHull B ⊆ {q : Point | normSq (q-p) ≤ d} := by
    apply convexHull_min _ (ball_convex p)
    rintro r ⟨b, hb, rfl⟩
    change normSq (realPoint b-p) ≤ d
    rw [swap]
    exact left b hb hp
  rw [swap]
  exact right hq

end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.squared_distance_on_hulls
