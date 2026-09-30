import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFiniteCapture

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

theorem local_projection_scale (q : UnitSquare) (normal : Point)
    (site : QPoint) (scale : ℝ) :
    localProjection q (scale • normal) site =
      scale * localProjection q normal site := by
  dsimp [localProjection]
  ring

theorem local_l1_scale (normal : Point) (scale : ℝ) (hs : 0 ≤ scale) :
    |(scale • normal).1| + |(scale • normal).2| =
      scale * (|normal.1| + |normal.2|) := by
  dsimp
  rw [abs_mul, abs_mul, abs_of_nonneg hs]
  ring

/-- Positive scaling does not change a lower-median comparison. -/
theorem local_median_bound_scale_pos
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (h : ℝ)
    (normal : Point) (scale : ℝ) (hs : 0 < scale)
    (hm : LocalMedianBound sites k q h normal) :
    LocalMedianBound sites k q h (scale • normal) := by
  classical
  obtain ⟨bound, hmedian, hsupport⟩ := hm
  refine ⟨scale * bound, ?_, ?_⟩
  · unfold MedianLowerBound at hmedian ⊢
    have hfilter :
        sites.filter (fun p => localProjection q (scale • normal) p < scale * bound) =
        sites.filter (fun p => localProjection q normal p < bound) := by
      ext p
      simp only [Finset.mem_filter]
      rw [local_projection_scale]
      simp only [(mul_lt_mul_iff_of_pos_left hs)]
    rw [hfilter]
    exact hmedian
  · rw [local_l1_scale normal scale hs.le]
    have hmul := mul_nonneg hs.le hsupport
    nlinarith

theorem local_median_bound_zero
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (h : ℝ)
    (hk : 0 < k) :
    LocalMedianBound sites k q h (0,0) := by
  refine ⟨0, ?_, ?_⟩
  · unfold MedianLowerBound
    simp [localProjection, hk]
  · simp

def realPairNormal (d : Point) : Point := (d.2, -d.1)

theorem orthogonal_normal_real_scaled (d normal : Point)
    (hd : d ≠ (0,0)) (hn : dot normal d = 0) :
    ∃ scale : ℝ, normal = scale • realPairNormal d := by
  by_cases hx : d.1 = 0
  · have hy : d.2 ≠ 0 := by
      intro hy
      apply hd
      exact Prod.ext hx hy
    have hn2 : normal.2 = 0 := by
      have he : normal.2 * d.2 = 0 := by
        dsimp [dot] at hn
        simpa [hx] using hn
      exact (mul_eq_zero.mp he).resolve_right hy
    refine ⟨normal.1 / d.2, ?_⟩
    apply Prod.ext
    · dsimp [realPairNormal]
      field_simp [hy]
    · simp [realPairNormal, hx, hn2]
  · refine ⟨-normal.2 / d.1, ?_⟩
    apply Prod.ext
    · dsimp [realPairNormal, dot] at hn ⊢
      field_simp [hx]
      nlinarith [hn]
    · dsimp [realPairNormal]
      field_simp [hx]

theorem orthogonal_normal_real_positive_ray (d normal : Point)
    (hd : d ≠ (0,0)) (hn : dot normal d = 0)
    (hnz : normal ≠ (0,0)) :
    (∃ scale : ℝ, 0 < scale ∧ normal = scale • realPairNormal d) ∨
    (∃ scale : ℝ, 0 < scale ∧ normal =
      scale • negPoint (realPairNormal d)) := by
  obtain ⟨scale, hscale⟩ := orthogonal_normal_real_scaled d normal hd hn
  have hsne : scale ≠ 0 := by
    intro hzero
    apply hnz
    rw [hscale, hzero]
    simp
    rfl
  rcases lt_or_gt_of_ne hsne with hsneg | hspos
  · right
    refine ⟨-scale, neg_pos.mpr hsneg, ?_⟩
    rw [hscale]
    apply Prod.ext <;> simp [realPairNormal, negPoint]
  · left
    exact ⟨scale, hspos, hscale⟩

/-- Every finite breakpoint direction is an axis, or a positive multiple
    of one of the two perpendiculars to a pair of site displacements. -/
theorem local_median_at_breakpoint_of_canonical
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (h : ℝ)
    (haxes : ∀ axis ∈ ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      LocalMedianBound sites k q h axis)
    (hpairs : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      LocalMedianBound sites k q h (pairPerp q a b) ∧
      LocalMedianBound sites k q h (negPoint (pairPerp q a b)))
    (sx sy : ℝ)
    (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1)
    (r : ℝ)
    (hr : r ∈ affineBreakpoints
      ((sites.image (fun p => localCoordinates q (realPoint p))).image
        (quadrantLine sx sy)))
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    LocalMedianBound sites k q h (quadrantNormal sx sy r) := by
  classical
  let lines :=
    (sites.image (fun p => localCoordinates q (realPoint p))).image
      (quadrantLine sx sy)
  change r ∈ affineBreakpoints lines at hr
  unfold affineBreakpoints at hr
  simp only [Finset.mem_insert] at hr
  rcases hr with hrzero | hrone | hrpair
  · subst r
    rcases hsy with rfl | rfl
    · simpa [quadrantNormal] using haxes (0,1) (by simp)
    · simpa [quadrantNormal] using haxes (0,-1) (by simp)
  · subst r
    rcases hsx with rfl | rfl
    · simpa [quadrantNormal] using haxes (1,0) (by simp)
    · simpa [quadrantNormal] using haxes (-1,0) (by simp)
  · obtain ⟨⟨lineA,lineB⟩, hpair, hcross⟩ := Finset.mem_image.mp hrpair
    obtain ⟨hlineA, hlineB⟩ := Finset.mem_product.mp hpair
    obtain ⟨localA, hlocalA, rfl⟩ := Finset.mem_image.mp hlineA
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hlocalA
    obtain ⟨localB, hlocalB, rfl⟩ := Finset.mem_image.mp hlineB
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hlocalB
    let A := localCoordinates q (realPoint a)
    let B := localCoordinates q (realPoint b)
    let lineA := quadrantLine sx sy A
    let lineB := quadrantLine sx sy B
    change affineCross lineA lineB = r at hcross
    by_cases hslope : lineA.1 = lineB.1
    · have hzero : r = 0 := by
        simpa [affineCross, hslope] using hcross.symm
      rw [hzero]
      rcases hsy with rfl | rfl
      · simpa [quadrantNormal] using haxes (0,1) (by simp)
      · simpa [quadrantNormal] using haxes (0,-1) (by simp)
    · let normal := quadrantNormal sx sy r
      have htie : dot normal A = dot normal B := by
        have ht := affine_tie_at_cross lineA lineB hslope
        rw [hcross] at ht
        simpa [lineA, lineB, normal, quadrant_line_value] using ht
      have hdorth : dot normal (B - A) = 0 := by
        dsimp [dot] at htie ⊢
        linarith
      have hdne : B - A ≠ (0,0) := by
        intro hd0
        have hAB : B = A := sub_eq_zero.mp hd0
        apply hslope
        simp [lineA, lineB, hAB]
      have hab : a ≠ b := by
        intro heq
        subst b
        exact hdne (by simp [A, B]; rfl)
      have hnz : normal ≠ (0,0) := by
        intro hn0
        have hnorm := quadrant_normal_l1 sx sy r hsx hsy hr0 hr1
        rw [← show normal = quadrantNormal sx sy r from rfl, hn0] at hnorm
        norm_num at hnorm
      have hperp : realPairNormal (B - A) = pairPerp q a b := by
        dsimp [realPairNormal, pairPerp, pairDX, pairDY, A, B,
          localCoordinates]
      rcases orthogonal_normal_real_positive_ray (B - A) normal hdne hdorth hnz with
        ⟨scale, hs, hscale⟩ | ⟨scale, hs, hscale⟩
      · rw [hperp] at hscale
        change LocalMedianBound sites k q h normal
        rw [hscale]
        exact local_median_bound_scale_pos sites k q h (pairPerp q a b)
          scale hs (hpairs a ha b hb hab).1
      · rw [hperp] at hscale
        change LocalMedianBound sites k q h normal
        rw [hscale]
        exact local_median_bound_scale_pos sites k q h
          (negPoint (pairPerp q a b)) scale hs (hpairs a ha b hb hab).2

/-- Four axes and both perpendicular directions for every ordered site pair
    suffice for majority capture at any threshold `k`. This is the producer
    interface for five- and seven-site features. -/
theorem majority_capture_of_axes_and_pairs
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h) (hstrict : h < 1 / 2) (hk : 0 < k)
    (haxes : ∀ axis ∈ ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      LocalMedianBound sites k q h axis)
    (hpairs : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      LocalMedianBound sites k q h (pairPerp q a b) ∧
      LocalMedianBound sites k q h (negPoint (pairPerp q a b))) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k q := by
  apply finite_median_majority_capture sites k q h hh hstrict hk
  intro sx sy hsx hsy r hr hr0 hr1
  exact local_median_at_breakpoint_of_canonical sites k q h haxes hpairs
    sx sy hsx hsy r hr hr0 hr1

theorem pair_perp_swap (q : UnitSquare) (a b : QPoint) :
    pairPerp q b a = negPoint (pairPerp q a b) := by
  apply Prod.ext <;>
    dsimp [pairPerp, pairDX, pairDY, negPoint] <;> ring

theorem neg_pair_perp_swap (q : UnitSquare) (a b : QPoint) :
    negPoint (pairPerp q b a) = pairPerp q a b := by
  rw [pair_perp_swap]
  apply Prod.ext <;> simp [negPoint]

/-- A finite roster with one orientation of each unordered site pair needs
    only two witnesses per roster entry. The cover condition is decidable for
    a concrete feature and independent of the square's angle. -/
theorem majority_capture_of_pair_cover
    (sites : Finset QPoint) (pairs : Finset (QPoint × QPoint))
    (k : ℕ) (q : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h) (hstrict : h < 1 / 2) (hk : 0 < k)
    (hcover : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      (a,b) ∈ pairs ∨ (b,a) ∈ pairs)
    (haxes : ∀ axis ∈ ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      LocalMedianBound sites k q h axis)
    (hpairs : ∀ ab ∈ pairs,
      LocalMedianBound sites k q h (pairPerp q ab.1 ab.2) ∧
      LocalMedianBound sites k q h
        (negPoint (pairPerp q ab.1 ab.2))) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k q := by
  apply majority_capture_of_axes_and_pairs sites k q h hh hstrict hk haxes
  intro a ha b hb hab
  rcases hcover a ha b hb hab with habpair | hbapair
  · exact hpairs (a,b) habpair
  · obtain ⟨hpos, hneg⟩ := hpairs (b,a) hbapair
    constructor
    · rw [neg_pair_perp_swap q a b] at hneg
      exact hneg
    · rw [pair_perp_swap q a b] at hpos
      exact hpos

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.local_median_bound_scale_pos
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.orthogonal_normal_real_positive_ray
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.majority_capture_of_axes_and_pairs
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.majority_capture_of_pair_cover
