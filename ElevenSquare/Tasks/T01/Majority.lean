import ElevenSquare.Pending.S06_BaselinePolyhedral
import ElevenSquare.Pending.S05_Trace
import Mathlib.Data.Finset.Powerset

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

def BaselineMajorityCapture (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) : Prop :=
  ∀ J ∈ sites.powersetCard k, ∃ p ∈ rationalHull J.toList, OpenSquare q p

theorem baseline_openSquare_isOpen (q : UnitSquare) : IsOpen {p | OpenSquare q p} := by
  have hx : Continuous (fun p : Point => |localX q p|) := by
    unfold localX dot
    dsimp
    continuity
  have hy : Continuous (fun p : Point => |localY q p|) := by
    unfold localY dot perp
    dsimp
    continuity
  exact (isOpen_lt hx continuous_const).inter (isOpen_lt hy continuous_const)

theorem baseline_hull_projection_le (vs : List QPoint) (f : Point →L[ℝ] ℝ) (u : ℝ)
    (hv : ∀ v ∈ vs, f (realPoint v) ≤ u) :
    ∀ p ∈ rationalHull vs, f p ≤ u := by
  have hconvex : Convex ℝ {p : Point | f p ≤ u} := by
    intro p hp q hq a b ha hb hab
    change f (a • p + b • q) ≤ u
    simp only [map_add, map_smul, smul_eq_mul]
    change f p ≤ u at hp
    change f q ≤ u at hq
    have h1 := mul_le_mul_of_nonneg_left hp ha
    have h2 := mul_le_mul_of_nonneg_left hq hb
    calc
      a * f p + b * f q ≤ a * u + b * u := add_le_add h1 h2
      _ = u := by rw [← add_mul, hab, one_mul]
  exact convexHull_min (by rintro p ⟨v, hv', rfl⟩; exact hv v hv') hconvex

theorem baseline_hull_projection_ge (vs : List QPoint) (f : Point →L[ℝ] ℝ) (u : ℝ)
    (hv : ∀ v ∈ vs, u ≤ f (realPoint v)) :
    ∀ p ∈ rationalHull vs, u ≤ f p := by
  intro p hp
  have hn := baseline_hull_projection_le vs (-f) (-u) (by
    intro v hv'
    change -f (realPoint v) ≤ -u
    exact neg_le_neg (hv v hv')) p hp
  change -f p ≤ -u at hn
  linarith

theorem baseline_majority_capacity_one (sites : Finset QPoint) (k : ℕ)
    (hsize : sites.card + 1 = 2 * k) (q r : UnitSquare)
    (hd : ∀ p, OpenSquare q p → OpenSquare r p → False)
    (hq : BaselineMajorityCapture sites k q)
    (hr : BaselineMajorityCapture sites k r) : False := by
  classical
  have hdisj : Disjoint {p | OpenSquare q p} {p | OpenSquare r p} := by
    apply Set.disjoint_left.mpr
    intro p hp hpr
    exact hd p hp hpr
  obtain ⟨f, u, hf, hg⟩ := geometric_hahn_banach_open_open
    (openSquare_convex q) (baseline_openSquare_isOpen q)
    (openSquare_convex r) (baseline_openSquare_isOpen r) hdisj
  let low := sites.filter (fun v => f (realPoint v) ≤ u)
  let high := sites.filter (fun v => ¬ f (realPoint v) ≤ u)
  have hcard : low.card + high.card = sites.card := by
    exact Finset.filter_card_add_filter_neg_card_eq_card (fun v => f (realPoint v) ≤ u)
  by_cases hl : k ≤ low.card
  · obtain ⟨J, hJ, hJk⟩ := Finset.exists_subset_card_eq hl
    have hJs : J ⊆ sites := hJ.trans (Finset.filter_subset _ _)
    obtain ⟨p, hp, hpr⟩ := hr J (Finset.mem_powersetCard.mpr ⟨hJs, hJk⟩)
    have hbound := baseline_hull_projection_le J.toList f u (by
      intro v hv
      exact (Finset.mem_filter.mp (hJ (by simpa using hv))).2) p hp
    exact (hg p hpr).not_le hbound
  · have hh : k ≤ high.card := by omega
    obtain ⟨J, hJ, hJk⟩ := Finset.exists_subset_card_eq hh
    have hJs : J ⊆ sites := hJ.trans (Finset.filter_subset _ _)
    obtain ⟨p, hp, hpq⟩ := hq J (Finset.mem_powersetCard.mpr ⟨hJs, hJk⟩)
    have hbound := baseline_hull_projection_ge J.toList f u (by
      intro v hv
      exact (lt_of_not_ge (Finset.mem_filter.mp (hJ (by simpa using hv))).2).le) p hp
    exact (hf p hpq).not_le hbound

theorem baseline_majority_unique_owner {S : ℝ} (P : Packing 11 S)
    (sites : Finset QPoint) (k : ℕ) (hsize : sites.card + 1 = 2 * k)
    (i j : Owner) (hi : BaselineMajorityCapture sites k (P.squares i))
    (hj : BaselineMajorityCapture sites k (P.squares j)) : i = j := by
  by_contra hij
  exact baseline_majority_capacity_one sites k hsize (P.squares i) (P.squares j)
    (fun p hp hq => P.interior_disjoint i j hij p ⟨hp, hq⟩) hi hj

end
end ElevenSquare.Tasks.T01
