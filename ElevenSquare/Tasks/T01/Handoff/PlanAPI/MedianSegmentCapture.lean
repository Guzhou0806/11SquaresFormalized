import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SegmentSquareCapture
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSupportOrder
import ElevenSquare.Tasks.T01.TripleCapture

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def localProjection (q : UnitSquare) (normal : Point) (site : QPoint) : ℝ :=
  normal.1 * localX q (realPoint site) +
  normal.2 * localY q (realPoint site)

/-- A finite lower-median bound in one local normal direction. -/
def LocalMedianBound (sites : Finset QPoint) (k : ℕ)
    (q : UnitSquare) (h : ℝ) (normal : Point) : Prop :=
  ∃ threshold : ℝ,
    MedianLowerBound sites k (localProjection q normal) threshold ∧
    0 ≤ threshold + h * (|normal.1| + |normal.2|)

theorem pair_local_support_of_median (sites : Finset QPoint)
    (a b : QPoint) (hab : a ≠ b) (ha : a ∈ sites) (hb : b ∈ sites)
    (q : UnitSquare) (h : ℝ) (normal : Point)
    (hm : LocalMedianBound sites 2 q h normal) :
    -h * (|normal.1| + |normal.2|) ≤
      max (localProjection q normal a) (localProjection q normal b) := by
  obtain ⟨threshold, hmedian, hcore⟩ := hm
  have hsub : ({a,b} : Finset QPoint) ⊆ sites := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption
  have hcard : ({a,b} : Finset QPoint).card = 2 := by
    simp [hab]
  obtain ⟨p, hp, hproj⟩ :=
    median_lower_bound_hits_subset sites {a,b} 2
      (localProjection q normal) threshold hmedian hsub hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact le_trans (by linarith : -h * (|normal.1| + |normal.2|) ≤ threshold)
      (hproj.trans (le_max_left _ _))
  · exact le_trans (by linarith : -h * (|normal.1| + |normal.2|) ≤ threshold)
      (hproj.trans (le_max_right _ _))

/-- Local displacement and its perpendicular support direction. -/
def pairDX (q : UnitSquare) (a b : QPoint) : ℝ :=
  localX q (realPoint b) - localX q (realPoint a)

def pairDY (q : UnitSquare) (a b : QPoint) : ℝ :=
  localY q (realPoint b) - localY q (realPoint a)

def pairPerp (q : UnitSquare) (a b : QPoint) : Point :=
  (pairDY q a b, -pairDX q a b)

def negPoint (v : Point) : Point := (-v.1, -v.2)

def AxialMedianBounds (sites : Finset QPoint) (q : UnitSquare) (h : ℝ) : Prop :=
  LocalMedianBound sites 2 q h (1, 0) ∧
  LocalMedianBound sites 2 q h (-1, 0) ∧
  LocalMedianBound sites 2 q h (0, 1) ∧
  LocalMedianBound sites 2 q h (0, -1)

/-- The four global axis medians and the two normals perpendicular to this
    pair imply all six segment-square support inequalities. -/
theorem pair_medians_imply_segment_bounds
    (sites : Finset QPoint) (a b : QPoint) (hab : a ≠ b)
    (ha : a ∈ sites) (hb : b ∈ sites)
    (q : UnitSquare) (h : ℝ)
    (haxes : AxialMedianBounds sites q h)
    (hperp : LocalMedianBound sites 2 q h (pairPerp q a b))
    (hperpNeg : LocalMedianBound sites 2 q h (negPoint (pairPerp q a b))) :
    SegmentSquareBounds q (realPoint a) (realPoint b) h := by
  let A := realPoint a
  let B := realPoint b
  let dx := pairDX q a b
  let dy := pairDY q a b
  have hxlo := pair_local_support_of_median sites a b hab ha hb q h (1, 0) haxes.1
  have hxhi := pair_local_support_of_median sites a b hab ha hb q h (-1, 0) haxes.2.1
  have hylo := pair_local_support_of_median sites a b hab ha hb q h (0, 1) haxes.2.2.1
  have hyhi := pair_local_support_of_median sites a b hab ha hb q h (0, -1) haxes.2.2.2
  have hClo := pair_local_support_of_median sites a b hab ha hb q h
    (pairPerp q a b) hperp
  have hChi := pair_local_support_of_median sites a b hab ha hb q h
    (negPoint (pairPerp q a b)) hperpNeg
  simp only [localProjection, abs_one, abs_zero, zero_add, add_zero,
    one_mul, neg_one_mul, zero_mul, neg_zero] at hxlo hxhi hylo hyhi
  have hxmax : -h ≤ max (localX q A) (localX q B) := by
    simpa [A, B] using hxlo
  have hxmin : min (localX q A) (localX q B) ≤ h := by
    simpa [A, B, max_neg_neg] using (neg_le_neg hxhi)
  have hymax : -h ≤ max (localY q A) (localY q B) := by
    simpa [A, B] using hylo
  have hymin : min (localY q A) (localY q B) ≤ h := by
    simpa [A, B, max_neg_neg] using (neg_le_neg hyhi)
  have hprojA : localProjection q (pairPerp q a b) a =
      localX q A * dy - localY q A * dx := by
    dsimp [localProjection, pairPerp, pairDX, pairDY, A, B, dx, dy]
    ring
  have hprojB : localProjection q (pairPerp q a b) b =
      localX q A * dy - localY q A * dx := by
    dsimp [localProjection, pairPerp, pairDX, pairDY, A, B, dx, dy]
    ring
  have hprojNegA : localProjection q (negPoint (pairPerp q a b)) a =
      -(localX q A * dy - localY q A * dx) := by
    dsimp [localProjection, negPoint, pairPerp, pairDX, pairDY, A, B, dx, dy]
    ring
  have hprojNegB : localProjection q (negPoint (pairPerp q a b)) b =
      -(localX q A * dy - localY q A * dx) := by
    dsimp [localProjection, negPoint, pairPerp, pairDX, pairDY, A, B, dx, dy]
    ring
  have hnorm : |(pairPerp q a b).1| + |(pairPerp q a b).2| =
      |dx| + |dy| := by
    dsimp [pairPerp, pairDX, pairDY, dx, dy]
    simp only [abs_neg]
    ring
  have hnormNeg : |(negPoint (pairPerp q a b)).1| +
      |(negPoint (pairPerp q a b)).2| = |dx| + |dy| := by
    dsimp [negPoint]
    simp only [abs_neg]
    exact hnorm
  have hcl : -h * (|dx| + |dy|) ≤
      localX q A * dy - localY q A * dx := by
    rw [hprojA, hprojB, max_self] at hClo
    rw [hnorm] at hClo
    exact hClo
  have hcu : localX q A * dy - localY q A * dx ≤
      h * (|dx| + |dy|) := by
    rw [hprojNegA, hprojNegB, max_self] at hChi
    rw [hnormNeg] at hChi
    linarith
  unfold SegmentSquareBounds
  refine ⟨hxmin, hxmax, hymin, hymax, ?_⟩
  have hcross : |localX q A * dy - localY q A * dx| ≤
      h * (|dx| + |dy|) := abs_le.mpr ⟨by linarith, hcu⟩
  simpa only [A, B, dx, dy, pairDX, pairDY] using hcross

theorem pair_capture_of_medians
    (sites : Finset QPoint) (a b : QPoint) (hab : a ≠ b)
    (ha : a ∈ sites) (hb : b ∈ sites)
    (q : UnitSquare) (h : ℝ) (hh : 0 ≤ h) (hstrict : h < 1 / 2)
    (haxes : AxialMedianBounds sites q h)
    (hperp : LocalMedianBound sites 2 q h (pairPerp q a b))
    (hperpNeg : LocalMedianBound sites 2 q h (negPoint (pairPerp q a b))) :
    ∃ p ∈ rationalHull [a,b], OpenSquare q p := by
  obtain ⟨p, hp, hq⟩ := segment_square_capture q (realPoint a) (realPoint b) h
    hh hstrict (pair_medians_imply_segment_bounds sites a b hab ha hb q h
      haxes hperp hperpNeg)
  refine ⟨p, ?_, hq⟩
  have heq : rationalHull [a,b] =
      convexHull ℝ ({realPoint a, realPoint b} : Set Point) := by
    unfold rationalHull
    congr 1
    ext x
    simp
  rw [heq]
  exact hp

/-- Four shared axis normals and two perpendicular normals for each of the
    three site pairs. Ten finite median checks replace three separate
    pairwise pose-region arguments. -/
def tripleMedianNormals (q : UnitSquare) (a b c : QPoint) : List Point :=
  [(1,0), (-1,0), (0,1), (0,-1),
    pairPerp q a b, negPoint (pairPerp q a b),
    pairPerp q a c, negPoint (pairPerp q a c),
    pairPerp q b c, negPoint (pairPerp q b c)]

def TripleMedianBounds (a b c : QPoint) (q : UnitSquare) (h : ℝ) : Prop :=
  ∀ n ∈ tripleMedianNormals q a b c,
    LocalMedianBound ({a,b,c} : Finset QPoint) 2 q h n

theorem triple_majority_of_median_bounds
    (a b c : QPoint) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (q : UnitSquare) (h : ℝ) (hh : 0 ≤ h) (hstrict : h < 1 / 2)
    (hm : TripleMedianBounds a b c q h) :
    BaselineMajorityCapture {a,b,c} 2 q := by
  let sites : Finset QPoint := {a,b,c}
  have haxes : AxialMedianBounds sites q h := by
    exact ⟨hm (1,0) (by simp [tripleMedianNormals]),
      hm (-1,0) (by simp [tripleMedianNormals]),
      hm (0,1) (by simp [tripleMedianNormals]),
      hm (0,-1) (by simp [tripleMedianNormals])⟩
  have hab' := pair_capture_of_medians sites a b hab (by simp [sites])
    (by simp [sites]) q h hh hstrict haxes
    (hm (pairPerp q a b) (by simp [tripleMedianNormals]))
    (hm (negPoint (pairPerp q a b)) (by simp [tripleMedianNormals]))
  have hac' := pair_capture_of_medians sites a c hac (by simp [sites])
    (by simp [sites]) q h hh hstrict haxes
    (hm (pairPerp q a c) (by simp [tripleMedianNormals]))
    (hm (negPoint (pairPerp q a c)) (by simp [tripleMedianNormals]))
  have hbc' := pair_capture_of_medians sites b c hbc (by simp [sites])
    (by simp [sites]) q h hh hstrict haxes
    (hm (pairPerp q b c) (by simp [tripleMedianNormals]))
    (hm (negPoint (pairPerp q b c)) (by simp [tripleMedianNormals]))
  exact triple_majority_capture a b c q hab' hac' hbc'

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.pair_local_support_of_median
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.pair_medians_imply_segment_bounds
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.triple_majority_of_median_bounds
