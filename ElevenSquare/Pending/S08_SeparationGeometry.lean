import ElevenSquare.BasicGeometry
import Mathlib.Algebra.Module.Prod

/-! Small geometric components for S08_GapFunctions. No case data, trigonometry,
or pending proof contracts are imported here. -/

namespace ElevenSquare.Pending.SeparationGeometry
noncomputable section

def EdgeNormal (q : UnitSquare) (v : Point) : Prop :=
  v = q.axis ∨ v = -q.axis ∨ v = perp q.axis ∨ v = -(perp q.axis)

theorem dot_neg_right (p v : Point) : dot p (-v) = -dot p v := by
  dsimp [dot]
  ring

theorem radius_neg (q : UnitSquare) (v : Point) :
    projectionRadius q (-v) = projectionRadius q v := by
  simp only [projectionRadius, dot_neg_right, abs_neg]

theorem edge_normal_neg {q : UnitSquare} {v : Point} (hv : EdgeNormal q v) :
    EdgeNormal q (-v) := by
  rcases hv with h | h | h | h
  · exact Or.inr (Or.inl (congrArg Neg.neg h))
  · exact Or.inl (by rw [h, neg_neg])
  · exact Or.inr (Or.inr (Or.inr (congrArg Neg.neg h)))
  · exact Or.inr (Or.inr (Or.inl (by rw [h, neg_neg])))

theorem edge_radius {q : UnitSquare} {v : Point} (hv : EdgeNormal q v) :
    projectionRadius q v = 1 / 2 := by
  rcases hv with h | h | h | h
  · rw [h, projectionRadius_axis]
  · rw [h, radius_neg, projectionRadius_axis]
  · rw [h, projectionRadius_perp_axis]
  · rw [h, radius_neg, projectionRadius_perp_axis]

theorem separation_reversed (a b : UnitSquare) (v : Point)
    (h : projectionRadius a v + projectionRadius b v ≤ dot (b.center-a.center) v) :
    projectionRadius b (-v) + projectionRadius a (-v) ≤ dot (a.center-b.center) (-v) := by
  rw [radius_neg, radius_neg]
  have he : dot (a.center-b.center) (-v) = dot (b.center-a.center) v := by
    dsimp [dot]
    ring
  rw [he, add_comm]
  exact h

/-- Separation on an owner's edge normal bounds every point of the other square,
not just a selected corner. Equality is allowed for touching boundaries. -/
theorem separated_points (a b : UnitSquare) (v : Point) (hv : EdgeNormal a v)
    (h : projectionRadius a v + projectionRadius b v ≤ dot (b.center-a.center) v)
    (p : Point) (hp : ClosedSquare b p) :
    1 / 2 ≤ dot (p-a.center) v := by
  have hb := (abs_le.mp (closed_projection_bound hp v)).1
  have he : dot (p-a.center) v = dot (p-b.center) v + dot (b.center-a.center) v := by
    dsimp [dot]
    ring
  rw [edge_radius hv] at h
  rw [he]
  linarith

theorem edge_normal_flags {q : UnitSquare} {v : Point} (hv : EdgeNormal q v) :
    ∃ perpendicular reverse : Bool,
      v = if reverse then -(if perpendicular then perp q.axis else q.axis)
          else (if perpendicular then perp q.axis else q.axis) := by
  rcases hv with h | h | h | h
  · exact ⟨false, false, h⟩
  · exact ⟨false, true, h⟩
  · exact ⟨true, false, h⟩
  · exact ⟨true, true, h⟩

theorem closed_affine_point (q : UnitSquare) (s t : ℝ)
    (hs : |s| ≤ 1/2) (ht : |t| ≤ 1/2) :
    ClosedSquare q (q.center + s • q.axis + t • perp q.axis) := by
  have hx : localX q (q.center + s • q.axis + t • perp q.axis) = s := by
    calc
      _ = s * normSq q.axis := by dsimp [localX, normSq, dot, perp]; ring
      _ = s := by rw [q.axis_unit, mul_one]
  have hy : localY q (q.center + s • q.axis + t • perp q.axis) = t := by
    calc
      _ = t * normSq q.axis := by dsimp [localY, normSq, dot, perp]; ring
      _ = t := by rw [q.axis_unit, mul_one]
  exact ⟨by simpa only [hx] using hs, by simpa only [hy] using ht⟩

/-- The finite axis list chooses an owner and bounds every point of its partner.
This is an adapter for a supplied separator, not a proof that a separator exists. -/
theorem separator_owner (a b : UnitSquare) (v : Point)
    (hv : v ∈ ([a.axis, -a.axis, perp a.axis, -(perp a.axis),
      b.axis, -b.axis, perp b.axis, -(perp b.axis)] : List Point))
    (h : projectionRadius a v + projectionRadius b v ≤ dot (b.center-a.center) v) :
    (∃ n, EdgeNormal a n ∧ ∀ p, ClosedSquare b p → 1/2 ≤ dot (p-a.center) n) ∨
    (∃ n, EdgeNormal b n ∧ ∀ p, ClosedSquare a p → 1/2 ≤ dot (p-b.center) n) := by
  have he : EdgeNormal a v ∨ EdgeNormal b v := by
    simpa only [EdgeNormal, List.mem_cons, List.not_mem_nil, or_false, or_assoc] using hv
  rcases he with ha | hb
  · exact Or.inl ⟨v, ha, separated_points a b v ha h⟩
  · have hn := edge_normal_neg hb
    exact Or.inr ⟨-v, hn, separated_points b a (-v) hn (separation_reversed a b v h)⟩

/-- The same signed halfplane expression used by `featureGap`, for arbitrary
points of the other square. No perturbation or differentiability is needed. -/
theorem halfplane_feature_flags (a b : UnitSquare) (n : Point)
    (hn : EdgeNormal a n)
    (hb : ∀ p, ClosedSquare b p → 1/2 ≤ dot (p-a.center) n) :
    ∃ perpendicular reverse : Bool, ∀ p, ClosedSquare b p →
      0 ≤ (if reverse then (-1:ℝ) else 1) *
        dot (p-a.center) (if perpendicular then perp a.axis else a.axis) - 1/2 := by
  obtain ⟨perpendicular, reverse, he⟩ := edge_normal_flags hn
  refine ⟨perpendicular, reverse, ?_⟩
  intro p hp
  have h := hb p hp
  rw [he] at h
  cases perpendicular <;> cases reverse <;>
    simp only [Bool.false_eq_true, ↓reduceIte, dot_neg_right, one_mul, neg_one_mul] at h ⊢ <;>
    linarith

/-- Full geometric bridge from any listed separator to a valid feature for one
of the two owners. Its premise is the still-needed separating-axis conclusion. -/
theorem separator_feature (a b : UnitSquare) (v : Point)
    (hv : v ∈ ([a.axis, -a.axis, perp a.axis, -(perp a.axis),
      b.axis, -b.axis, perp b.axis, -(perp b.axis)] : List Point))
    (h : projectionRadius a v + projectionRadius b v ≤ dot (b.center-a.center) v) :
    (∃ perpendicular reverse : Bool, ∀ p, ClosedSquare b p →
      0 ≤ (if reverse then (-1:ℝ) else 1) *
        dot (p-a.center) (if perpendicular then perp a.axis else a.axis) - 1/2) ∨
    (∃ perpendicular reverse : Bool, ∀ p, ClosedSquare a p →
      0 ≤ (if reverse then (-1:ℝ) else 1) *
        dot (p-b.center) (if perpendicular then perp b.axis else b.axis) - 1/2) := by
  rcases separator_owner a b v hv h with ⟨n, hn, hb⟩ | ⟨n, hn, hb⟩
  · exact Or.inl (halfplane_feature_flags a b n hn hb)
  · exact Or.inr (halfplane_feature_flags b a n hn hb)

#print axioms dot_neg_right
#print axioms radius_neg
#print axioms edge_normal_neg
#print axioms edge_radius
#print axioms separation_reversed
#print axioms separated_points
#print axioms edge_normal_flags
#print axioms closed_affine_point
#print axioms separator_owner
#print axioms halfplane_feature_flags
#print axioms separator_feature

end
end ElevenSquare.Pending.SeparationGeometry
