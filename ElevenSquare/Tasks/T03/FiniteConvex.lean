import ElevenSquare.Tasks.T03.TriangleCover

namespace ElevenSquare.Pending.T03
noncomputable section

structure Barycentric3 where
  a : QPoint
  b : QPoint
  c : QPoint
  wa : ℕ
  wb : ℕ
  wc : ℕ
  denominator : ℕ
  deriving DecidableEq, Inhabited

def Barycentric3.check (w : Barycentric3) (vertices : List QPoint) (p : QPoint) : Bool :=
  decide (0 < w.denominator ∧ w.a ∈ vertices ∧ w.b ∈ vertices ∧ w.c ∈ vertices ∧
    w.wa+w.wb+w.wc = w.denominator ∧
    (w.wa:ℚ)*w.a.1+(w.wb:ℚ)*w.b.1+(w.wc:ℚ)*w.c.1=(w.denominator:ℚ)*p.1 ∧
    (w.wa:ℚ)*w.a.2+(w.wb:ℚ)*w.b.2+(w.wc:ℚ)*w.c.2=(w.denominator:ℚ)*p.2)

theorem Barycentric3.sound (w : Barycentric3) (vertices : List QPoint) (p : QPoint)
    (h : w.check vertices p = true) (F : Set Point) (hF : Convex ℝ F)
    (hvertices : ∀ v ∈ vertices, realPoint v ∈ F) : realPoint p ∈ F := by
  obtain ⟨hd,ha,hb,hc,hs,hx,hy⟩ := of_decide_eq_true h
  have hd' : (0:ℝ) < w.denominator := by exact_mod_cast hd
  have hs' : (w.wa:ℝ)+(w.wb:ℝ)+(w.wc:ℝ)=(w.denominator:ℝ) := by exact_mod_cast hs
  have hx' := congrArg (fun x : ℚ => (x:ℝ)) hx
  have hy' := congrArg (fun x : ℚ => (x:ℝ)) hy
  push_cast at hx' hy'
  have hsum : (w.wa:ℝ)/w.denominator+(w.wb:ℝ)/w.denominator+
      (w.wc:ℝ)/w.denominator=1 := by
    rw [← add_div,← add_div,hs',div_self (ne_of_gt hd')]
  have heq : realPoint p = ((w.wa:ℝ)/w.denominator) • realPoint w.a+
      ((w.wb:ℝ)/w.denominator) • realPoint w.b+
      ((w.wc:ℝ)/w.denominator) • realPoint w.c := by
    ext <;> dsimp [realPoint]
    · field_simp [ne_of_gt hd']
      nlinarith only [hx']
    · field_simp [ne_of_gt hd']
      nlinarith only [hy']
  rw [heq]
  exact convex_three_mem F hF _ _ _ (hvertices w.a ha) (hvertices w.b hb)
    (hvertices w.c hc) _ _ _ (div_nonneg (Nat.cast_nonneg _) hd'.le)
    (div_nonneg (Nat.cast_nonneg _) hd'.le) (div_nonneg (Nat.cast_nonneg _) hd'.le) hsum

theorem Barycentric3.mem_hull (w : Barycentric3) (vertices : List QPoint) (p : QPoint)
    (h : w.check vertices p = true) : realPoint p ∈ rationalHull vertices := by
  exact w.sound vertices p h _ (convex_convexHull ℝ _)
    (fun v hv => subset_convexHull ℝ _ ⟨v,hv,rfl⟩)

/-- The forbidden region is convex because both the owned hull and strict core
are convex. Every use must supply both of those geometric hypotheses. -/
theorem forbiddenCenters_convex (K Q : Set Point) (hK : Convex ℝ K) (hQ : Convex ℝ Q) :
    Convex ℝ (forbiddenCenters K Q) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨kx,hkx,vx,hvx,rfl⟩ := hx
  obtain ⟨ky,hky,vy,hvy,rfl⟩ := hy
  refine ⟨a • kx+b • ky,hK hkx hky ha hb hab,
    a • vx+b • vy,hQ hvx hvy ha hb hab,?_⟩
  ext <;> dsimp <;> ring

theorem rational_difference_forbidden (ks qs : List QPoint) (k v p : QPoint)
    (hk : k ∈ ks) (hv : v ∈ qs) (he : p = k-v) :
    realPoint p ∈ forbiddenCenters (rationalHull ks) (rationalHull qs) := by
  refine ⟨realPoint k,subset_convexHull ℝ _ ⟨k,hk,rfl⟩,
    realPoint v,subset_convexHull ℝ _ ⟨v,hv,rfl⟩,?_⟩
  rw [he]
  simp [realPoint]

end
end ElevenSquare.Pending.T03
