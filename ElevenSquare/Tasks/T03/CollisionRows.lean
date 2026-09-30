import ElevenSquare.Tasks.T03.PhysicalRows

namespace ElevenSquare.Pending.T03
noncomputable section

def PhysicalPartnerCover (old : List QPoint) (before after : List PoseRow) : Prop :=
  ∀ q, RowsContain before q → ContainedAtCap q →
    (rationalHull old ⊆ {p | OpenSquare q p}) → RowsContain after q

/-- The partner quantifier covers every pose in the full recorded partner rows. -/
structure UniversalCollisionRegion (i : Owner) (lo hi : ℚ) where
  partner : Owner
  distinct : i ≠ partner
  vertices : List QPoint
  partnerRows : List PoseRow
  collision : ∀ q r t, (lo:ℝ) ≤ t → t ≤ (hi:ℝ) → q.axis=chartAxis t →
    q.center ∈ rationalHull vertices → RowsContain partnerRows r →
    ∃ p, OpenSquare q p ∧ OpenSquare r p

theorem UniversalCollisionRegion.pose {i : Owner} {lo hi : ℚ}
    (w : UniversalCollisionRegion i lo hi) (prior : Owner → List QPoint)
    (rows : Owner → List PoseRow)
    (hbind : PhysicalPartnerCover (prior w.partner) (rows w.partner) w.partnerRows)
    (q : UnitSquare) (t : ℝ) (ha : (lo:ℝ) ≤ t) (hb : t ≤ (hi:ℝ))
    (haxis : q.axis=chartAxis t) (hx : q.center ∈ rationalHull w.vertices) :
    PhysicalCollisionPose prior rows i q := by
  refine ⟨w.partner,w.distinct,?_⟩
  intro r hr hc hold
  exact w.collision q r t ha hb haxis hx (hbind r hr hc hold)

structure CollisionRowGeometry (prior : Owner → List QPoint) (i : Owner)
    (chosen : List QPoint) where
  lo : ℚ
  hi : ℚ
  global_bounds : 0 ≤ lo ∧ hi ≤ 1
  domain : List IntegerPlane
  kept : Option (List IntegerPlane)
  collisions : List (UniversalCollisionRegion i lo hi)
  cover : ∀ q t, (lo:ℝ) ≤ t → t ≤ (hi:ℝ) → q.axis=chartAxis t →
    q.center ∈ IntegerCarrier domain → keptCenter kept q.center ∨ ForbiddenPose prior i q ∨
      ∃ w ∈ collisions, q.center ∈ rationalHull w.vertices
  owned : ∀ q t, (lo:ℝ) ≤ t → t ≤ (hi:ℝ) → q.axis=chartAxis t →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) → keptCenter kept q.center →
    ∀ p ∈ chosen, OpenSquare q (realPoint p)

def CollisionRowGeometry.toForward {prior : Owner → List QPoint} {i : Owner}
    {chosen : List QPoint} (g : CollisionRowGeometry prior i chosen)
    (rows : Owner → List PoseRow)
    (hbind : ∀ w ∈ g.collisions, PhysicalPartnerCover (prior w.partner) (rows w.partner) w.partnerRows) :
    ForwardRowGeometry prior rows i chosen where
  lo := g.lo
  hi := g.hi
  global_bounds := g.global_bounds
  domain := g.domain
  kept := g.kept
  cover := by
    intro q t ha hb haxis hx
    rcases g.cover q t ha hb haxis hx with hk | hf | ⟨w,hw,hx⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr (w.pose prior rows (hbind w hw) q t ha hb haxis hx))
  owned := g.owned

end
end ElevenSquare.Pending.T03
