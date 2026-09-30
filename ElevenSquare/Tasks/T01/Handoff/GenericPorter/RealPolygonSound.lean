import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare ElevenSquare.Pending
noncomputable section

structure RealHalfplane where
  a : ℝ
  b : ℝ
  c : ℝ

@[ext] theorem RealHalfplane.ext {h k : RealHalfplane}
    (ha : h.a = k.a) (hb : h.b = k.b) (hc : h.c = k.c) : h = k := by
  cases h
  cases k
  simp_all

def RealHalfplane.contains (h : RealHalfplane) (p : Point) : Prop :=
  h.a * p.1 + h.b * p.2 ≤ h.c

def RealHalfplane.scale (d : ℝ) (h : RealHalfplane) : RealHalfplane :=
  ⟨d*h.a,d*h.b,d*h.c⟩

theorem real_halfplane_scale_sound (h : RealHalfplane) (d : ℝ) (p : Point)
    (hd : 0 < d) (hh : (h.scale d).contains p) : h.contains p := by
  simp only [RealHalfplane.scale, RealHalfplane.contains] at hh ⊢
  have hs : d * (h.a*p.1+h.b*p.2) ≤ d*h.c := by
    convert hh using 1 <;> ring
  exact (mul_le_mul_left hd).mp hs

def RealPolygon.carrier (hs : List RealHalfplane) : Set Point :=
  {p | ∀ h ∈ hs, h.contains p}

def realEdge (u v : Point) : RealHalfplane :=
  ⟨v.2-u.2, u.1-v.1, (v.2-u.2)*u.1+(u.1-v.1)*u.2⟩

theorem real_edge_contains (u v p : Point) :
    (realEdge u v).contains p ↔
      0 ≤ baselineCross (v-u) (p-u) := by
  dsimp [realEdge, RealHalfplane.contains, baselineCross]
  constructor <;> intro h <;> nlinarith

def RealPolygonCheck (vs : List Point) (hs : List RealHalfplane) : Prop :=
  vs ≠ [] ∧ ∀ v ∈ vs, ∃ u ∈ vs, ∃ w ∈ vs,
    realEdge u v ∈ hs ∧ realEdge v w ∈ hs ∧
    0 < baselineCross (w-v) (u-v)

theorem realHull_isClosed (vs : List Point) :
    IsClosed (convexHull ℝ {p | p ∈ vs}) := by
  have he : {p : Point | p ∈ vs} = (↑vs.toFinset : Set Point) := by
    ext p
    simp
  rw [he]
  exact (Finset.finite_toSet vs.toFinset).isClosed_convexHull

/-- A sound finite polygon rule for arbitrary real vertices and moving
    halfplanes, applied separately at each chart parameter. -/
theorem real_polygon_check_sound (vs : List Point) (hs : List RealHalfplane)
    (hc : RealPolygonCheck vs hs) :
    RealPolygon.carrier hs ⊆ convexHull ℝ {v | v ∈ vs} := by
  classical
  intro p hp
  by_contra hout
  obtain ⟨f, b, hvs, hpb⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (realHull_isClosed vs) hout
  have hn : vs.toFinset.Nonempty := by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hc.1
    exact ⟨v, by simpa using hv⟩
  obtain ⟨v, hv, hmax⟩ := vs.toFinset.exists_max_image (fun v => f v) hn
  have hv' : v ∈ vs := by simpa using hv
  obtain ⟨u, hu, w, hw, huv, hvw, hturn⟩ := hc.2 v hv'
  have hl := (real_edge_contains v w p).mp (hp _ hvw)
  have hr := (real_edge_contains u v p).mp (hp _ huv)
  have hr' : 0 ≤ baselineCross (p-v) (u-v) := by
    dsimp [baselineCross] at hr ⊢
    nlinarith
  have hfp := baseline_wedge_bound f u v w p hturn hl hr'
    (hmax u (by simpa using hu)) (hmax w (by simpa using hw))
  have hvm : v ∈ convexHull ℝ {v | v ∈ vs} :=
    subset_convexHull ℝ _ hv'
  exact (hvs _ hvm).not_le (hpb.le.trans hfp)

/-- A moving facet can be a positive rescaling of an actual edge. This
    support form avoids requiring literal equality of facet coefficients. -/
def RealPolygonSupportCheck (vs : List Point) (hs : List RealHalfplane) : Prop :=
  vs ≠ [] ∧ ∀ v ∈ vs, ∃ u ∈ vs, ∃ w ∈ vs,
    (∀ p ∈ RealPolygon.carrier hs, (realEdge u v).contains p) ∧
    (∀ p ∈ RealPolygon.carrier hs, (realEdge v w).contains p) ∧
    0 < baselineCross (w-v) (u-v)

theorem real_polygon_support_sound (vs : List Point) (hs : List RealHalfplane)
    (hc : RealPolygonSupportCheck vs hs) :
    RealPolygon.carrier hs ⊆ convexHull ℝ {v | v ∈ vs} := by
  classical
  intro p hp
  by_contra hout
  obtain ⟨f, b, hvs, hpb⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (realHull_isClosed vs) hout
  have hn : vs.toFinset.Nonempty := by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hc.1
    exact ⟨v, by simpa using hv⟩
  obtain ⟨v, hv, hmax⟩ := vs.toFinset.exists_max_image (fun v => f v) hn
  have hv' : v ∈ vs := by simpa using hv
  obtain ⟨u, hu, w, hw, huv, hvw, hturn⟩ := hc.2 v hv'
  have hl := (real_edge_contains v w p).mp (hvw p hp)
  have hr := (real_edge_contains u v p).mp (huv p hp)
  have hr' : 0 ≤ baselineCross (p-v) (u-v) := by
    dsimp [baselineCross] at hr ⊢
    nlinarith
  have hfp := baseline_wedge_bound f u v w p hturn hl hr'
    (hmax u (by simpa using hu)) (hmax w (by simpa using hw))
  have hvm : v ∈ convexHull ℝ {v | v ∈ vs} :=
    subset_convexHull ℝ _ hv'
  exact (hvs _ hvm).not_le (hpb.le.trans hfp)

#print axioms real_polygon_check_sound
#print axioms real_polygon_support_sound

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter
