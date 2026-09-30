import ElevenSquare.Pending.S05_OwnedHull

/-! Convex vertex reduction for the capture source's closed center polygons.
The angular parameter remains universal; there is no center sampling. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def recenteredSquare (q : UnitSquare) : UnitSquare where
  center := (0, 0)
  axis := q.axis
  axis_unit := q.axis_unit

theorem hull_coordinate_bounds (vs : List QPoint)
    (lx ux ly uy : ℚ)
    (hvertices : ∀ v ∈ vs,
      lx ≤ v.1 ∧ v.1 ≤ ux ∧ ly ≤ v.2 ∧ v.2 ≤ uy)
    {p : Point} (hp : p ∈ rationalHull vs) :
    (lx : ℝ) ≤ p.1 ∧ p.1 ≤ (ux : ℝ) ∧
      (ly : ℝ) ≤ p.2 ∧ p.2 ≤ (uy : ℝ) := by
  let box : Set Point := {p |
    (lx : ℝ) ≤ p.1 ∧ p.1 ≤ (ux : ℝ) ∧
    (ly : ℝ) ≤ p.2 ∧ p.2 ≤ (uy : ℝ)}
  have hconv : Convex ℝ box := by
    have hs : box = (Set.Icc (lx : ℝ) ux ×ˢ Set.Icc (ly : ℝ) uy) := by
      ext p
      simp only [box, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
      tauto
    rw [hs]
    exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hbase : {p : Point | ∃ v ∈ vs, p = realPoint v} ⊆ box := by
    rintro p ⟨v, hv, rfl⟩
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hvertices v hv
    change (lx : ℝ) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) ≤ (ux : ℝ) ∧
      (ly : ℝ) ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) ≤ (uy : ℝ)
    exact ⟨by exact_mod_cast hx0, by exact_mod_cast hx1,
      by exact_mod_cast hy0, by exact_mod_cast hy1⟩
  exact (convexHull_min hbase hconv) hp

theorem openSquare_of_center_hull (q : UnitSquare) (vs : List QPoint)
    (w : Point) (hc : q.center ∈ rationalHull vs)
    (hvertices : ∀ v ∈ vs,
      OpenSquare (recenteredSquare q) (w-realPoint v)) :
    OpenSquare q w := by
  let C : Set Point := {c | OpenSquare (recenteredSquare q) (w-c)}
  let f : Point →ᵃ[ℝ] Point :=
    AffineMap.const ℝ Point w - AffineMap.id ℝ Point
  have hconv : Convex ℝ C := by
    simpa only [C, f, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply,
      AffineMap.id_apply, Set.preimage_setOf_eq] using
      (openSquare_convex (recenteredSquare q)).affine_preimage f
  have hbase : {c : Point | ∃ v ∈ vs, c = realPoint v} ⊆ C := by
    rintro c ⟨v, hv, rfl⟩
    exact hvertices v hv
  have hq : OpenSquare (recenteredSquare q) (w-q.center) :=
    (convexHull_min hbase hconv) hc
  have hz : (w-q.center)-(0,0) = w-q.center := by
    apply Prod.ext <;> simp [Prod.fst_sub, Prod.snd_sub]
  simpa [OpenSquare, recenteredSquare, localX, localY, hz] using hq

end
end ElevenSquare.Tasks.T07
