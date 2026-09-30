import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianAffineBreakpoints
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.Convex.Combination

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
open scoped Pointwise
noncomputable section

/-- Every nonzero planar normal is a positive L1 scale of a point on one of
    the four quadrant segments. -/
theorem l1_normal_decomposition (normal : Point)
    (hn : 0 < |normal.1| + |normal.2|) :
    ∃ sx sy r : ℝ,
      (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
      0 ≤ r ∧ r ≤ 1 ∧
      normal = (|normal.1| + |normal.2|) • quadrantNormal sx sy r := by
  let R := |normal.1| + |normal.2|
  have hR : 0 < R := hn
  have hRne : R ≠ 0 := ne_of_gt hR
  let r := |normal.1| / R
  have hr0 : 0 ≤ r := div_nonneg (abs_nonneg _) hR.le
  have hr1 : r ≤ 1 := (div_le_one hR).mpr (by dsimp [R]; linarith [abs_nonneg normal.2])
  obtain ⟨sx, hsx, hxs⟩ : ∃ sx : ℝ,
      (sx = 1 ∨ sx = -1) ∧ sx * |normal.1| = normal.1 := by
    by_cases hx : 0 ≤ normal.1
    · exact ⟨1, Or.inl rfl, by simp [abs_of_nonneg hx]⟩
    · have hx' : normal.1 ≤ 0 := le_of_lt (lt_of_not_ge hx)
      exact ⟨-1, Or.inr rfl, by simp [abs_of_nonpos hx']⟩
  obtain ⟨sy, hsy, hys⟩ : ∃ sy : ℝ,
      (sy = 1 ∨ sy = -1) ∧ sy * |normal.2| = normal.2 := by
    by_cases hy : 0 ≤ normal.2
    · exact ⟨1, Or.inl rfl, by simp [abs_of_nonneg hy]⟩
    · have hy' : normal.2 ≤ 0 := le_of_lt (lt_of_not_ge hy)
      exact ⟨-1, Or.inr rfl, by simp [abs_of_nonpos hy']⟩
  refine ⟨sx, sy, r, hsx, hsy, hr0, hr1, ?_⟩
  apply Prod.ext
  · dsimp [quadrantNormal, r]
    field_simp [hRne]
    nlinarith [hxs]
  · dsimp [quadrantNormal, r]
    field_simp [hRne]
    dsimp [R]
    nlinarith [hys]

/-- Four finite lists of L1-quadrant support checks imply the support
    inequality for every real normal. The lists depend only on site-pair
    crossings; no convex hull facets are supplied. -/
theorem finite_quadrant_checks_imply_all_support
    (sites : Finset Point) (hnonempty : sites.Nonempty)
    (center : Point) (h : ℝ)
    (hbreak : ∀ sx sy : ℝ,
      (sx = 1 ∨ sx = -1) → (sy = 1 ∨ sy = -1) →
      ∀ r ∈ affineBreakpoints (sites.image (quadrantLine sx sy)),
        0 ≤ r → r ≤ 1 →
        ∃ p ∈ sites,
          dot (quadrantNormal sx sy r) center ≤
            dot (quadrantNormal sx sy r) p + h)
    (normal : Point) :
    ∃ p ∈ sites,
      dot normal center ≤ dot normal p + h * (|normal.1| + |normal.2|) := by
  let R := |normal.1| + |normal.2|
  by_cases hR : R = 0
  · have hcoord1 : normal.1 = 0 := by
      have hnon1 := abs_nonneg normal.1
      have hnon2 := abs_nonneg normal.2
      have habs : |normal.1| = 0 := by dsimp [R] at hR; linarith
      exact abs_eq_zero.mp habs
    have hcoord2 : normal.2 = 0 := by
      have hnon1 := abs_nonneg normal.1
      have hnon2 := abs_nonneg normal.2
      have habs : |normal.2| = 0 := by dsimp [R] at hR; linarith
      exact abs_eq_zero.mp habs
    obtain ⟨p, hp⟩ := hnonempty
    refine ⟨p, hp, ?_⟩
    simp [dot, hcoord1, hcoord2, R, hR]
  · have hRpos : 0 < R := lt_of_le_of_ne
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) (Ne.symm hR)
    obtain ⟨sx, sy, r, hsx, hsy, hr0, hr1, hdecomp⟩ :=
      l1_normal_decomposition normal hRpos
    obtain ⟨p, hp, hq⟩ :=
      finite_quadrant_support sites hnonempty center h sx sy
        (hbreak sx sy hsx hsy) r hr0 hr1
    have hdot (x : Point) :
        dot normal x = R * dot (quadrantNormal sx sy r) x := by
      rw [hdecomp]
      dsimp [dot, quadrantNormal]
      ring
    refine ⟨p, hp, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hq hRpos.le
    rw [hdot center, hdot p]
    convert hm using 1 <;> ring

/-- The four vertices of a centered axis-aligned square. -/
def centeredCoreCorners (h : ℝ) : Finset Point :=
  { (h,h), (h,-h), (-h,h), (-h,-h) }

theorem quadrant_normal_l1 (sx sy r : ℝ)
    (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |(quadrantNormal sx sy r).1| + |(quadrantNormal sx sy r).2| = 1 := by
  have hrneg : r - 1 ≤ 0 := by linarith
  rcases hsx with rfl | rfl <;> rcases hsy with rfl | rfl <;>
    dsimp [quadrantNormal] <;>
    simp [abs_of_nonneg hr0, abs_of_nonneg (sub_nonneg.mpr hr1)]
  all_goals
    rw [abs_of_nonpos hrneg]
    ring

theorem centered_core_support (h : ℝ) (normal : Point) :
    ∃ c ∈ centeredCoreCorners h,
      dot normal c = h * (|normal.1| + |normal.2|) := by
  by_cases hx : 0 ≤ normal.1
  · by_cases hy : 0 ≤ normal.2
    · refine ⟨(h,h), by simp [centeredCoreCorners], ?_⟩
      simp [dot, abs_of_nonneg hx, abs_of_nonneg hy]
      ring
    · have hy' : normal.2 ≤ 0 := le_of_lt (lt_of_not_ge hy)
      refine ⟨(h,-h), by simp [centeredCoreCorners], ?_⟩
      simp [dot, abs_of_nonneg hx, abs_of_nonpos hy']
      ring
  · have hx' : normal.1 ≤ 0 := le_of_lt (lt_of_not_ge hx)
    by_cases hy : 0 ≤ normal.2
    · refine ⟨(-h,h), by simp [centeredCoreCorners], ?_⟩
      simp [dot, abs_of_nonpos hx', abs_of_nonneg hy]
      ring
    · have hy' : normal.2 ≤ 0 := le_of_lt (lt_of_not_ge hy)
      refine ⟨(-h,-h), by simp [centeredCoreCorners], ?_⟩
      simp [dot, abs_of_nonpos hx', abs_of_nonpos hy']
      ring

/-- The finite-normal checks force the site hull to meet the closed square
    of half-width `h`. This is the planar geometric step for arbitrary site
    count and arbitrary selected subset. -/
theorem finite_normal_closed_square_capture
    (sites : Finset Point) (hnonempty : sites.Nonempty) (h : ℝ) (hh : 0 ≤ h)
    (hbreak : ∀ sx sy : ℝ,
      (sx = 1 ∨ sx = -1) → (sy = 1 ∨ sy = -1) →
      ∀ r ∈ affineBreakpoints (sites.image (quadrantLine sx sy)),
        0 ≤ r → r ≤ 1 →
        ∃ p ∈ sites,
          dot (quadrantNormal sx sy r) (0,0) ≤
            dot (quadrantNormal sx sy r) p + h) :
    ∃ p ∈ convexHull ℝ (↑sites : Set Point),
      |p.1| ≤ h ∧ |p.2| ≤ h := by
  classical
  let corners := centeredCoreCorners h
  have hsupport : ∀ normal : Point,
      ∃ v ∈ (sites + corners).toList,
        dot normal (0,0) ≤ dot normal v := by
    intro normal
    obtain ⟨p, hp, hsite⟩ :=
      finite_quadrant_checks_imply_all_support sites hnonempty (0,0) h
        hbreak normal
    obtain ⟨c, hc, hcore⟩ := centered_core_support h normal
    refine ⟨p + c, by simpa using Finset.add_mem_add hp hc, ?_⟩
    dsimp [dot] at hsite hcore ⊢
    nlinarith
  have hzero : (0 : Point) ∈ convexHull ℝ (↑(sites + corners) : Set Point) := by
    convert finite_hull_of_all_dot_support (sites + corners).toList (0,0)
      hsupport using 1
    congr 1
    ext v
    simp
  rw [Finset.coe_add, convexHull_add] at hzero
  obtain ⟨p, hp, c, hc, hsum⟩ := hzero
  have hcornerBound :
      convexHull ℝ (↑corners : Set Point) ⊆
        Set.Icc (-h) h ×ˢ Set.Icc (-h) h := by
    apply convexHull_min
    · intro v hv
      change v ∈ centeredCoreCorners h at hv
      simp [centeredCoreCorners] at hv
      rcases hv with hv | hv | hv | hv <;> subst v <;>
        simp [Set.mem_prod, Set.mem_Icc, hh]
    · exact (convex_Icc (-h) h).prod (convex_Icc (-h) h)
  have hcb := hcornerBound hc
  have hfirst : p.1 = -c.1 := by
    have he := congrArg Prod.fst hsum
    dsimp at he
    linarith
  have hsecond : p.2 = -c.2 := by
    have he := congrArg Prod.snd hsum
    dsimp at he
    linarith
  refine ⟨p, hp, ?_, ?_⟩
  · rw [hfirst]
    have hc1 : -h ≤ c.1 ∧ c.1 ≤ h := hcb.1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [hsecond]
    have hc2 : -h ≤ c.2 ∧ c.2 ≤ h := hcb.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.l1_normal_decomposition
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.finite_quadrant_checks_imply_all_support
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.finite_normal_closed_square_capture
