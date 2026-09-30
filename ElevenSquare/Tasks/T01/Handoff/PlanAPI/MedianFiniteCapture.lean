import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianQuadrantSupport
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSegmentCapture

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- Coordinates in the moving unit-square frame. -/
def localCoordinates (q : UnitSquare) (p : Point) : Point :=
  (localX q p, localY q p)

/-- Inverse from square-frame coordinates to the plane. -/
def fromLocalCoordinates (q : UnitSquare) (v : Point) : Point :=
  q.center + v.1 • q.axis + v.2 • perp q.axis

theorem from_local_coordinates_left (q : UnitSquare) (p : Point) :
    fromLocalCoordinates q (localCoordinates q p) = p := by
  have hr := coordinate_reconstruction (p - q.center) q.axis q.axis_unit
  apply Prod.ext
  · have hx := congrArg Prod.fst hr
    dsimp [fromLocalCoordinates, localCoordinates, localX, localY, dot, perp] at hx ⊢
    linarith
  · have hy := congrArg Prod.snd hr
    dsimp [fromLocalCoordinates, localCoordinates, localX, localY, dot, perp] at hy ⊢
    linarith

theorem from_local_coordinates_right (q : UnitSquare) (v : Point) :
    localCoordinates q (fromLocalCoordinates q v) = v := by
  have hunit := q.axis_unit
  dsimp [normSq, dot] at hunit
  apply Prod.ext
  · dsimp [fromLocalCoordinates, localCoordinates, localX, localY, dot, perp]
    nlinarith [congrArg (fun z : ℝ => v.1 * z) hunit]
  · dsimp [fromLocalCoordinates, localCoordinates, localX, localY, dot, perp]
    nlinarith [congrArg (fun z : ℝ => v.2 * z) hunit]

def fromLocalAffineMap (q : UnitSquare) : Point →ᵃ[ℝ] Point where
  toFun := fromLocalCoordinates q
  linear := {
    toFun := fun v => v.1 • q.axis + v.2 • perp q.axis
    map_add' := by
      intro x y
      apply Prod.ext <;> dsimp [perp] <;> ring
    map_smul' := by
      intro a x
      apply Prod.ext <;> dsimp [perp] <;> ring
  }
  map_vadd' := by
    intro p v
    apply Prod.ext <;> dsimp [fromLocalCoordinates, perp] <;> ring

theorem local_hull_preimage (q : UnitSquare) (sites : Finset QPoint)
    (u : Point)
    (hu : u ∈ convexHull ℝ
      (↑(sites.image (fun p => localCoordinates q (realPoint p))) : Set Point)) :
    fromLocalCoordinates q u ∈ rationalHull sites.toList := by
  classical
  let f := fromLocalAffineMap q
  have hpre : Convex ℝ (f ⁻¹' rationalHull sites.toList) :=
    (convex_convexHull ℝ _).affine_preimage f
  have hsites :
      (↑(sites.image (fun p => localCoordinates q (realPoint p))) : Set Point) ⊆
        f ⁻¹' rationalHull sites.toList := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    change fromLocalCoordinates q (localCoordinates q (realPoint p)) ∈
      rationalHull sites.toList
    rw [from_local_coordinates_left]
    exact subset_convexHull ℝ _ ⟨p, by simpa using hp, rfl⟩
  exact (convexHull_min hsites hpre) hu

/-- Median support at finitely many axis and site-pair crossing normals
    captures one selected subset, regardless of its cardinality. -/
theorem subset_capture_of_median_breakpoints
    (sites subset : Finset QPoint) (k : ℕ) (q : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h) (hstrict : h < 1 / 2)
    (hk : 0 < k) (hsubset : subset ⊆ sites) (hcard : subset.card = k)
    (hmed : ∀ sx sy : ℝ,
      (sx = 1 ∨ sx = -1) → (sy = 1 ∨ sy = -1) →
      ∀ r ∈ affineBreakpoints
          ((subset.image (fun p => localCoordinates q (realPoint p))).image
            (quadrantLine sx sy)),
        0 ≤ r → r ≤ 1 →
        LocalMedianBound sites k q h (quadrantNormal sx sy r)) :
    ∃ p ∈ rationalHull subset.toList, OpenSquare q p := by
  classical
  let localSites := subset.image (fun p => localCoordinates q (realPoint p))
  have hsubne : subset.Nonempty := Finset.card_pos.mp (by simpa [hcard] using hk)
  have hlocalne : localSites.Nonempty := hsubne.image _
  have hbreak : ∀ sx sy : ℝ,
      (sx = 1 ∨ sx = -1) → (sy = 1 ∨ sy = -1) →
      ∀ r ∈ affineBreakpoints (localSites.image (quadrantLine sx sy)),
        0 ≤ r → r ≤ 1 →
        ∃ p ∈ localSites,
          dot (quadrantNormal sx sy r) (0,0) ≤
            dot (quadrantNormal sx sy r) p + h := by
    intro sx sy hsx hsy r hr hr0 hr1
    let normal := quadrantNormal sx sy r
    obtain ⟨b, hmedian, hbound⟩ := hmed sx sy hsx hsy r hr hr0 hr1
    obtain ⟨p, hp, hprojection⟩ :=
      median_lower_bound_hits_subset sites subset k
        (localProjection q normal) b hmedian hsubset hcard
    have hnorm : |normal.1| + |normal.2| = 1 :=
      quadrant_normal_l1 sx sy r hsx hsy hr0 hr1
    rw [hnorm] at hbound
    refine ⟨localCoordinates q (realPoint p),
      Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    dsimp [normal, localProjection, localCoordinates, dot] at hprojection ⊢
    linarith
  obtain ⟨v, hv, hvbound⟩ :=
    finite_normal_closed_square_capture localSites hlocalne h hh hbreak
  refine ⟨fromLocalCoordinates q v, local_hull_preimage q subset v hv, ?_⟩
  have hcoordinate := from_local_coordinates_right q v
  change (localX q (fromLocalCoordinates q v),
    localY q (fromLocalCoordinates q v)) = v at hcoordinate
  have hx := congrArg Prod.fst hcoordinate
  have hy := congrArg Prod.snd hcoordinate
  dsimp at hx hy
  unfold OpenSquare
  rw [hx, hy]
  exact ⟨lt_of_le_of_lt hvbound.1 hstrict,
    lt_of_le_of_lt hvbound.2 hstrict⟩

/-- One finite collection of median support directions, generated from all
    site-pair crossings on the four L1 quadrants, proves majority capture for
    *every* selected `k`-subset. No subset hull certificates are required. -/
theorem finite_median_majority_capture
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h) (hstrict : h < 1 / 2) (hk : 0 < k)
    (hmed : ∀ sx sy : ℝ,
      (sx = 1 ∨ sx = -1) → (sy = 1 ∨ sy = -1) →
      ∀ r ∈ affineBreakpoints
          ((sites.image (fun p => localCoordinates q (realPoint p))).image
            (quadrantLine sx sy)),
        0 ≤ r → r ≤ 1 →
        LocalMedianBound sites k q h (quadrantNormal sx sy r)) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k q := by
  classical
  intro subset hmem
  obtain ⟨hsubset, hcard⟩ := Finset.mem_powersetCard.mp hmem
  apply subset_capture_of_median_breakpoints sites subset k q h hh hstrict
    hk hsubset hcard
  intro sx sy hsx hsy r hr hr0 hr1
  apply hmed sx sy hsx hsy r _ hr0 hr1
  have hlocal :
      subset.image (fun p => localCoordinates q (realPoint p)) ⊆
      sites.image (fun p => localCoordinates q (realPoint p)) :=
    Finset.image_subset_image hsubset
  have hlines :
      (subset.image (fun p => localCoordinates q (realPoint p))).image
          (quadrantLine sx sy) ⊆
      (sites.image (fun p => localCoordinates q (realPoint p))).image
          (quadrantLine sx sy) := Finset.image_subset_image hlocal
  exact affineBreakpoints_mono hlines hr

/-- Four sign choices for the L1-normal quadrants. -/
def medianQuadrantSigns : Finset Point :=
  { (1,1), (1,-1), (-1,1), (-1,-1) }

/-- The finite directions generated by all site-pair projection crossings.
    Directions outside the quadrant interval are discarded. -/
noncomputable def medianBreakpointNormals (sites : Finset QPoint)
    (q : UnitSquare) : Finset Point := by
  classical
  exact medianQuadrantSigns.biUnion (fun signs =>
    ((affineBreakpoints
      ((sites.image (fun p => localCoordinates q (realPoint p))).image
        (quadrantLine signs.1 signs.2))).filter
          (fun r => 0 ≤ r ∧ r ≤ 1)).image
            (quadrantNormal signs.1 signs.2))

theorem quadrant_normal_mem_medianBreakpointNormals
    (sites : Finset QPoint) (q : UnitSquare)
    (sx sy r : ℝ)
    (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1)
    (hr : r ∈ affineBreakpoints
      ((sites.image (fun p => localCoordinates q (realPoint p))).image
        (quadrantLine sx sy)))
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    quadrantNormal sx sy r ∈ medianBreakpointNormals sites q := by
  classical
  unfold medianBreakpointNormals
  apply Finset.mem_biUnion.mpr
  refine ⟨(sx,sy), ?_, ?_⟩
  · rcases hsx with rfl | rfl <;> rcases hsy with rfl | rfl <;>
      simp [medianQuadrantSigns]
  · apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨hr, ⟨hr0,hr1⟩⟩, rfl⟩

/-- Reusable arbitrary-cardinality median-to-majority API. The hypothesis is
    one finite collection of median checks, shared by every `k`-subset. -/
theorem majority_capture_of_finite_median_normals
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h) (hstrict : h < 1 / 2) (hk : 0 < k)
    (hmed : ∀ normal ∈ medianBreakpointNormals sites q,
      LocalMedianBound sites k q h normal) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k q := by
  apply finite_median_majority_capture sites k q h hh hstrict hk
  intro sx sy hsx hsy r hr hr0 hr1
  exact hmed _ (quadrant_normal_mem_medianBreakpointNormals sites q sx sy r
    hsx hsy hr hr0 hr1)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.local_hull_preimage
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.subset_capture_of_median_breakpoints
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.finite_median_majority_capture
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.majority_capture_of_finite_median_normals
