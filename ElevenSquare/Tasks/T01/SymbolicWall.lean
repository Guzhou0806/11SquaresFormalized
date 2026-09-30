import ElevenSquare.Tasks.T01.Wall

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- The exact wall margin, without rounding an entire angle interval down. -/
def exactWallMargin (t : ℝ) : ℝ := (baselineCos t + baselineSin t) / 2

theorem exactWallMargin_formula (t : ℝ) :
    exactWallMargin t = (1 - t^2 + 2*t) / (2 * (1+t^2)) := by
  unfold exactWallMargin baselineCos baselineSin
  rw [← add_div, div_div]
  congr 1
  ring

/-- Every cell facet is constant; container facets depend affinely on the
exact wall margin. Their normal vectors do not depend on the orientation. -/
structure SymbolicWallFacet where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

def SymbolicWallFacet.bound (f : SymbolicWallFacet) (t : ℝ) : ℝ :=
  (f.c : ℝ) + f.d * exactWallMargin t

def SymbolicWallFacet.contains (f : SymbolicWallFacet) (t : ℝ) (p : Point) : Prop :=
  (f.a : ℝ) * p.1 + f.b * p.2 ≤ f.bound t

def SymbolicWallFacet.ofHalfplane (h : Halfplane) : SymbolicWallFacet :=
  ⟨h.a, h.b, h.c, 0⟩

def SymbolicWallFacet.determinant (f g : SymbolicWallFacet) : ℚ :=
  f.a * g.b - f.b * g.a

/-- These inverse-matrix formulas automatically establish both normal
identities. Concrete certificates need only check their signs and margin. -/
def SymbolicWallFacet.dualFirst (f g : SymbolicWallFacet) (direction : Point) : ℝ :=
  (direction.1 * g.b - direction.2 * g.a) / (f.determinant g : ℝ)

def SymbolicWallFacet.dualSecond (f g : SymbolicWallFacet) (direction : Point) : ℝ :=
  ((f.a : ℝ) * direction.2 - f.b * direction.1) / (f.determinant g : ℝ)

theorem symbolic_wall_dual_normals (f g : SymbolicWallFacet) (direction : Point)
    (hd : f.determinant g ≠ 0) :
    f.dualFirst g direction * f.a + f.dualSecond g direction * g.a = direction.1 ∧
    f.dualFirst g direction * f.b + f.dualSecond g direction * g.b = direction.2 := by
  have hd' : (f.determinant g : ℝ) ≠ 0 := by exact_mod_cast hd
  unfold SymbolicWallFacet.dualFirst SymbolicWallFacet.dualSecond
  constructor
  all_goals field_simp [hd']
  all_goals simp only [SymbolicWallFacet.determinant, Rat.cast_sub, Rat.cast_mul]
  all_goals ring

def symbolicWallSlab (cell : Fin 16) : List SymbolicWallFacet :=
  [⟨-1, 0, 0, -1⟩, ⟨1, 0, baselineRationalCap, -1⟩,
   ⟨0, -1, 0, -1⟩, ⟨0, 1, baselineRationalCap, -1⟩] ++
    (baselineCellPolygon cell).map SymbolicWallFacet.ofHalfplane

theorem symbolic_wall_slab_contains (q : UnitSquare) (cell : Fin 16) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell cell (normalizeCenter q.center)) :
    ∀ f ∈ symbolicWallSlab cell, f.contains t q.center := by
  have hb := baseline_contained_axis_bounds q coverCap hcont
  rw [ha] at hb
  change exactWallMargin t ≤ q.center.1 ∧
    q.center.1 ≤ coverCap - exactWallMargin t ∧
    exactWallMargin t ≤ q.center.2 ∧
    q.center.2 ≤ coverCap - exactWallMargin t at hb
  have hc := baselineCellPolygon_contains hcell
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals
      simp only [SymbolicWallFacet.contains, SymbolicWallFacet.bound]
      push_cast
      try rw [baselineRationalCap_cast]
      linarith [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hf
    simpa [SymbolicWallFacet.contains, SymbolicWallFacet.bound,
      SymbolicWallFacet.ofHalfplane, Halfplane.contains] using hc h hh

/-- The four local directions with the positive denominator `1+t²` cleared. -/
def chartDirectionNumerator (t : ℝ) : Fin 4 → Point :=
  ![(1-t^2, 2*t), (-(1-t^2), -2*t), (-2*t, 1-t^2), (2*t, -(1-t^2))]

theorem point_owned_of_direction_numerators (q : UnitSquare) (p : Point) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hb : ∀ k : Fin 4,
      dot (chartDirectionNumerator t k) (q.center - p) < (1+t^2)/2) :
    OpenSquare q p := by
  have hd : 0 < 1+t^2 := by positivity
  have hx : dot (chartDirectionNumerator t 0) (q.center - p) =
      -(1+t^2) * localX q p := by
    simp [chartDirectionNumerator, localX, ha, chartAxis, dot]
    field_simp [ne_of_gt hd]
    <;> ring
  have hy : dot (chartDirectionNumerator t 2) (q.center - p) =
      -(1+t^2) * localY q p := by
    simp [chartDirectionNumerator, localY, ha, chartAxis, dot, perp]
    field_simp [ne_of_gt hd]
    <;> ring
  have hxn : dot (chartDirectionNumerator t 1) (q.center - p) =
      (1+t^2) * localX q p := by
    have hn : dot (chartDirectionNumerator t 1) (q.center - p) =
        -dot (chartDirectionNumerator t 0) (q.center - p) := by
      simp [chartDirectionNumerator, dot]
      <;> ring
    rw [hn, hx]
    ring
  have hyn : dot (chartDirectionNumerator t 3) (q.center - p) =
      (1+t^2) * localY q p := by
    have hn : dot (chartDirectionNumerator t 3) (q.center - p) =
        -dot (chartDirectionNumerator t 2) (q.center - p) := by
      simp [chartDirectionNumerator, dot]
      <;> ring
    rw [hn, hy]
    ring
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  rw [hx] at h0
  rw [hxn] at h1
  rw [hy] at h2
  rw [hyn] at h3
  refine ⟨abs_lt.mpr ⟨?_, ?_⟩, abs_lt.mpr ⟨?_, ?_⟩⟩
  all_goals apply (mul_lt_mul_iff_of_pos_left hd).mp
  all_goals nlinarith

/-- Two nonnegative dual weights suffice in dimension two. This analytic
lemma is uniform in the angle; polynomial certificates can check its weights,
normal identity, and strict margin over a whole interval. -/
theorem symbolic_wall_dual_bound (f g : SymbolicWallFacet) (t : ℝ)
    (center p direction : Point) (u v : ℝ)
    (hf : f.contains t center) (hg : g.contains t center)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : u * f.a + v * g.a = direction.1)
    (hy : u * f.b + v * g.b = direction.2)
    (hm : u * f.bound t + v * g.bound t < dot direction p + (1+t^2)/2) :
    dot direction (center - p) < (1+t^2)/2 := by
  have hfu := mul_le_mul_of_nonneg_left hf hu
  have hgv := mul_le_mul_of_nonneg_left hg hv
  have he : dot direction center =
      u * ((f.a : ℝ)*center.1 + f.b*center.2) +
      v * ((g.a : ℝ)*center.1 + g.b*center.2) := by
    dsimp [dot]
    rw [← hx, ← hy]
    ring
  have hs : dot direction center ≤ u*f.bound t + v*g.bound t := by
    rw [he]
    exact add_le_add hfu hgv
  have he' : dot direction (center-p) = dot direction center - dot direction p := by
    simp [dot]
    <;> ring
  rw [he']
  linarith only [hs, hm]

/-- A complete exact dual cover at the square's actual angle implies strict
ownership. No subdivision, sampled angle, or polygon vertex is assumed. -/
theorem symbolic_wall_point_owned (q : UnitSquare) (cell : Fin 16)
    (p : Point) (t : ℝ) (ha : q.axis = chartAxis t)
    (hcont : ∀ x, ClosedSquare q x → InContainer coverCap x)
    (hcell : ClosedCell cell (normalizeCenter q.center))
    (hdual : ∀ k : Fin 4, ∃ f ∈ symbolicWallSlab cell,
      ∃ g ∈ symbolicWallSlab cell, ∃ u v : ℝ,
        0 ≤ u ∧ 0 ≤ v ∧
        u * f.a + v * g.a = (chartDirectionNumerator t k).1 ∧
        u * f.b + v * g.b = (chartDirectionNumerator t k).2 ∧
        u * f.bound t + v * g.bound t <
          dot (chartDirectionNumerator t k) p + (1+t^2)/2) :
    OpenSquare q p := by
  apply point_owned_of_direction_numerators q p t ha
  intro k
  obtain ⟨f, hf, g, hg, u, v, hu, hv, hx, hy, hm⟩ := hdual k
  exact symbolic_wall_dual_bound f g t q.center p (chartDirectionNumerator t k)
    u v (symbolic_wall_slab_contains q cell t ha hcont hcell f hf)
    (symbolic_wall_slab_contains q cell t ha hcont hcell g hg) hu hv hx hy hm

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.symbolic_wall_slab_contains
#print axioms ElevenSquare.Tasks.T01.symbolic_wall_dual_normals
#print axioms ElevenSquare.Tasks.T01.point_owned_of_direction_numerators
#print axioms ElevenSquare.Tasks.T01.symbolic_wall_dual_bound
#print axioms ElevenSquare.Tasks.T01.symbolic_wall_point_owned
