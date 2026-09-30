import ElevenSquare.Pending.Types
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ElevenSquare.Pending
noncomputable section

abbrev BaselineCombination := List (ℕ × ℚ)

def baselineZeroHalfplane : Halfplane := ⟨0, 0, 0⟩

def baselineCombinationSum (hs : Polygon) : BaselineCombination → Halfplane
  | [] => baselineZeroHalfplane
  | (i, w) :: ws =>
    let h := hs.getD i baselineZeroHalfplane
    let s := baselineCombinationSum hs ws
    ⟨w * h.a + s.a, w * h.b + s.b, w * h.c + s.c⟩

def BaselineCombinationValid (hs : Polygon) (ws : BaselineCombination) : Prop :=
  ∀ iw ∈ ws, iw.1 < hs.length ∧ 0 ≤ iw.2

instance (hs : Polygon) (ws : BaselineCombination) :
    Decidable (BaselineCombinationValid hs ws) := by
  unfold BaselineCombinationValid
  infer_instance

theorem baseline_combination_sum_sound (hs : Polygon) (ws : BaselineCombination)
    (hw : BaselineCombinationValid hs ws) (p : Point) (hp : p ∈ hs.carrier) :
    (baselineCombinationSum hs ws).contains p := by
  induction ws with
  | nil => simp [baselineCombinationSum, baselineZeroHalfplane, Halfplane.contains]
  | cons iw ws ih =>
    have hiw := hw iw (by simp)
    have hrest : BaselineCombinationValid hs ws := by
      intro e he
      exact hw e (by simp [he])
    have hh := hp (hs.getD iw.1 baselineZeroHalfplane) (by
      rw [List.getD_eq_get hs baselineZeroHalfplane hiw.1]
      exact List.get_mem ..)
    have hh' := mul_le_mul_of_nonneg_left hh
      (show (0 : ℝ) ≤ iw.2 by exact_mod_cast hiw.2)
    have hr := ih hrest
    rcases iw with ⟨i, w⟩
    dsimp [baselineCombinationSum, Halfplane.contains] at hh' hr ⊢
    push_cast
    nlinarith

def BaselineImplicationCheck (hs : Polygon) (h : Halfplane)
    (ws : BaselineCombination) : Prop :=
  BaselineCombinationValid hs ws ∧
  (baselineCombinationSum hs ws).a = h.a ∧
  (baselineCombinationSum hs ws).b = h.b ∧
  (baselineCombinationSum hs ws).c ≤ h.c

instance (hs : Polygon) (h : Halfplane) (ws : BaselineCombination) :
    Decidable (BaselineImplicationCheck hs h ws) := by
  unfold BaselineImplicationCheck
  infer_instance

theorem baseline_implication_check_sound (hs : Polygon) (h : Halfplane)
    (ws : BaselineCombination) (hc : BaselineImplicationCheck hs h ws)
    (p : Point) (hp : p ∈ hs.carrier) : h.contains p := by
  have ha := baseline_combination_sum_sound hs ws hc.1 p hp
  dsimp [Halfplane.contains] at ha ⊢
  rw [hc.2.1, hc.2.2.1] at ha
  exact ha.trans (by exact_mod_cast hc.2.2.2)

def BaselineStrictImplicationCheck (hs : Polygon) (h : Halfplane)
    (ws : BaselineCombination) : Prop :=
  BaselineCombinationValid hs ws ∧
  (baselineCombinationSum hs ws).a = h.a ∧
  (baselineCombinationSum hs ws).b = h.b ∧
  (baselineCombinationSum hs ws).c < h.c

instance (hs : Polygon) (h : Halfplane) (ws : BaselineCombination) :
    Decidable (BaselineStrictImplicationCheck hs h ws) := by
  unfold BaselineStrictImplicationCheck
  infer_instance

theorem baseline_strict_implication_check_sound (hs : Polygon) (h : Halfplane)
    (ws : BaselineCombination) (hc : BaselineStrictImplicationCheck hs h ws)
    (p : Point) (hp : p ∈ hs.carrier) :
    (h.a : ℝ) * p.1 + (h.b : ℝ) * p.2 < h.c := by
  have ha := baseline_combination_sum_sound hs ws hc.1 p hp
  dsimp [Halfplane.contains] at ha
  rw [hc.2.1, hc.2.2.1] at ha
  exact ha.trans_lt (by exact_mod_cast hc.2.2.2)

def baselineEdge (u v : QPoint) : Halfplane :=
  ⟨v.2 - u.2, u.1 - v.1, (v.2 - u.2) * u.1 + (u.1 - v.1) * u.2⟩

def baselineCross (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

theorem baseline_edge_contains (u v : QPoint) (p : Point) :
    (baselineEdge u v).contains p ↔
      0 ≤ baselineCross (realPoint v - realPoint u) (p - realPoint u) := by
  dsimp [baselineEdge, Halfplane.contains, baselineCross, realPoint]
  push_cast
  constructor <;> intro h <;> nlinarith

def BaselinePolygonCheck (vs : List QPoint) (hs : Polygon) : Prop :=
  vs ≠ [] ∧ ∀ v ∈ vs, ∃ u ∈ vs, ∃ w ∈ vs,
    baselineEdge u v ∈ hs ∧ baselineEdge v w ∈ hs ∧
    0 < (w.1 - v.1) * (u.2 - v.2) - (w.2 - v.2) * (u.1 - v.1)

instance (vs : List QPoint) (hs : Polygon) :
    Decidable (BaselinePolygonCheck vs hs) := by
  unfold BaselinePolygonCheck
  infer_instance

theorem baseline_linear_coordinates (f : Point →L[ℝ] ℝ) (p : Point) :
    f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
  have he : p = p.1 • (1, 0) + p.2 • (0, 1) := by ext <;> simp
  calc
    f p = f (p.1 • (1, 0) + p.2 • (0, 1)) := congrArg f he
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

theorem baseline_wedge_bound (f : Point →L[ℝ] ℝ) (u v w p : Point)
    (hturn : 0 < baselineCross (w - v) (u - v))
    (hleft : 0 ≤ baselineCross (w - v) (p - v))
    (hright : 0 ≤ baselineCross (p - v) (u - v))
    (hu : f u ≤ f v) (hw : f w ≤ f v) : f p ≤ f v := by
  have h1 := mul_nonpos_of_nonneg_of_nonpos hright (sub_nonpos.mpr hw)
  have h2 := mul_nonpos_of_nonneg_of_nonpos hleft (sub_nonpos.mpr hu)
  have he : baselineCross (w - v) (u - v) * (f p - f v) =
      baselineCross (p - v) (u - v) * (f w - f v) +
      baselineCross (w - v) (p - v) * (f u - f v) := by
    rw [baseline_linear_coordinates f p, baseline_linear_coordinates f v,
      baseline_linear_coordinates f w, baseline_linear_coordinates f u]
    dsimp [baselineCross]
    ring
  have hnon : baselineCross (w - v) (u - v) * (f p - f v) ≤ 0 := by
    rw [he]
    linarith
  by_contra h
  exact (not_lt_of_ge hnon) (mul_pos hturn (sub_pos.mpr (lt_of_not_ge h)))

theorem baseline_rationalHull_isClosed (vs : List QPoint) :
    IsClosed (rationalHull vs) := by
  have he : {p | ∃ v ∈ vs, p = realPoint v} =
      realPoint '' (↑vs.toFinset : Set QPoint) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  unfold rationalHull
  rw [he]
  exact ((Finset.finite_toSet vs.toFinset).image realPoint).isClosed_convexHull

theorem baseline_polygon_check_sound (vs : List QPoint) (hs : Polygon)
    (hc : BaselinePolygonCheck vs hs) : hs.carrier ⊆ rationalHull vs := by
  classical
  intro p hp
  by_contra hout
  obtain ⟨f, b, hvs, hpb⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (baseline_rationalHull_isClosed vs) hout
  have hn : vs.toFinset.Nonempty := by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hc.1
    exact ⟨v, by simpa using hv⟩
  obtain ⟨v, hv, hmax⟩ := vs.toFinset.exists_max_image (fun v => f (realPoint v)) hn
  have hv' : v ∈ vs := by simpa using hv
  obtain ⟨u, hu, w, hw, huv, hvw, hturn⟩ := hc.2 v hv'
  have hl := (baseline_edge_contains v w p).mp (hp _ hvw)
  have hr := (baseline_edge_contains u v p).mp (hp _ huv)
  have hr' : 0 ≤ baselineCross (p - realPoint v) (realPoint u - realPoint v) := by
    dsimp [baselineCross, realPoint] at hr ⊢
    nlinarith
  have ht : 0 < baselineCross (realPoint w - realPoint v) (realPoint u - realPoint v) := by
    dsimp [baselineCross, realPoint]
    exact_mod_cast hturn
  have hfp := baseline_wedge_bound f (realPoint u) (realPoint v) (realPoint w) p ht hl hr'
    (hmax u (by simpa using hu)) (hmax w (by simpa using hw))
  have hvm : realPoint v ∈ rationalHull vs :=
    subset_convexHull ℝ _ ⟨v, hv', rfl⟩
  exact (hvs _ hvm).not_le (hpb.le.trans hfp)

end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.baseline_combination_sum_sound
#print axioms ElevenSquare.Pending.baseline_implication_check_sound
#print axioms ElevenSquare.Pending.baseline_strict_implication_check_sound
#print axioms ElevenSquare.Pending.baseline_edge_contains
#print axioms ElevenSquare.Pending.baseline_linear_coordinates
#print axioms ElevenSquare.Pending.baseline_wedge_bound
#print axioms ElevenSquare.Pending.baseline_rationalHull_isClosed
#print axioms ElevenSquare.Pending.baseline_polygon_check_sound
