import ElevenSquare.Tasks.T03.TraceAssembly

namespace ElevenSquare.Pending.T03
noncomputable section

def IntegerRow.intersect (r : IntegerRow) (ls : List IntegerPlane) : IntegerRow :=
  ⟨r.lo,r.hi,ls++r.planes⟩

theorem IntegerRow.intersect_contains (r : IntegerRow) (ls : List IntegerPlane) (q : UnitSquare) :
    (r.intersect ls).row.contains q ↔ r.row.contains q ∧ q.center ∈ IntegerCarrier ls := by
  constructor
  · intro h
    have hc := (r.intersect ls).center_mem q h
    have hr : q.center ∈ IntegerCarrier r.planes := fun l hl => hc l (List.mem_append_right _ hl)
    refine ⟨⟨?_,h.2⟩,fun l hl => hc l (List.mem_append_left _ hl)⟩
    simpa only [integerCarrier_as_polygon] using hr
  · rintro ⟨hr,hl⟩
    refine ⟨?_,hr.2⟩
    change q.center ∈ Polygon.carrier ((ls++r.planes).map IntegerPlane.rational)
    rw [← integerCarrier_as_polygon]
    intro l h
    rcases List.mem_append.mp h with h | h
    · exact hl l h
    · exact r.center_mem q hr l h

theorem rowsContain_singleton (r : PoseRow) (q : UnitSquare) :
    RowsContain [r] q ↔ r.contains q := by
  constructor
  · rintro ⟨s,hs,hq⟩
    have he : s=r := by simpa using hs
    subst s; exact hq
  · intro hq; exact ⟨r,by simp,hq⟩

def keptCenter (kept : Option (List IntegerPlane)) (p : Point) : Prop :=
  match kept with
  | none => False
  | some ls => p ∈ IntegerCarrier ls

/-- Geometric data for one closed angular bin; the prior hull vector is explicit. -/
structure RowGeometry (prior : Owner → List QPoint) (i : Owner) (chosen : List QPoint) where
  lo : ℚ
  hi : ℚ
  domain : List IntegerPlane
  kept : Option (List IntegerPlane)
  cover : ∀ q t, (lo:ℝ) ≤ t → t ≤ (hi:ℝ) → q.axis=chartAxis t →
    q.center ∈ IntegerCarrier domain →
    keptCenter kept q.center ∨ ForbiddenPose prior i q
  owned : ∀ q t, (lo:ℝ) ≤ t → t ≤ (hi:ℝ) → q.axis=chartAxis t →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
    keptCenter kept q.center →
    ∀ p ∈ chosen, OpenSquare q (realPoint p)

def RowGeometry.resultRows {prior : Owner → List QPoint} {i : Owner} {chosen : List QPoint}
    (g : RowGeometry prior i chosen) (r : IntegerRow) : List PoseRow :=
  match g.kept with
  | none => []
  | some ls => [(r.intersect ls).row]

theorem RowGeometry.result_contains {prior : Owner → List QPoint} {i : Owner} {chosen : List QPoint}
    (g : RowGeometry prior i chosen) (r : IntegerRow) (q : UnitSquare) :
    RowsContain (g.resultRows r) q ↔ r.row.contains q ∧ keptCenter g.kept q.center := by
  cases h : g.kept with
  | none => simp [resultRows,h,RowsContain,keptCenter]
  | some ls =>
    simp only [resultRows,h,rowsContain_singleton]
    exact r.intersect_contains ls q

def RowGeometry.certificate {prior : Owner → List QPoint} {i : Owner} {chosen : List QPoint}
    (g : RowGeometry prior i chosen) (r : IntegerRow)
    (input : ∀ q, r.row.contains q →
      (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
      q.center ∈ IntegerCarrier g.domain ∧
        ∃ t : ℝ, (g.lo:ℝ) ≤ t ∧ t ≤ (g.hi:ℝ) ∧ q.axis=chartAxis t) :
    RowsCertificate prior i chosen where
  before := [r.row]
  after := g.resultRows r
  back := by
    intro q hq
    exact (rowsContain_singleton _ q).mpr ((g.result_contains r q).mp hq).1
  cover := by
    intro q hq hold
    have hr := (rowsContain_singleton _ q).mp hq
    obtain ⟨hc,t,ht0,ht1,haxis⟩ := input q hr hold
    rcases g.cover q t ht0 ht1 haxis hc with hk | hf
    · exact Or.inl ((g.result_contains r q).mpr ⟨hr,hk⟩)
    · exact Or.inr hf
  owned := by
    intro q hq hold
    obtain ⟨hr,hk⟩ := (g.result_contains r q).mp hq
    obtain ⟨_,t,ht0,ht1,haxis⟩ := input q hr hold
    exact g.owned q t ht0 ht1 haxis hold hk

def RowGeometry.checkedCertificate {prior : Owner → List QPoint} {i : Owner} {chosen : List QPoint}
    (g : RowGeometry prior i chosen) (r : IntegerRow) (w : RowInputCertificate)
    (h : w.check r (prior i) = true) (hlo : w.lo=g.lo) (hhi : w.hi=g.hi)
    (hd : w.domain=g.domain) : RowsCertificate prior i chosen :=
  g.certificate r (by
    intro q hq hold
    have hw := w.sound r (prior i) h q hq hold
    simpa only [hlo,hhi,hd] using hw)

end
end ElevenSquare.Pending.T03
