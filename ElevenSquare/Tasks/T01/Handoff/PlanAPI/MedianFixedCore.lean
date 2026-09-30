import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianCanonicalNormals
import ElevenSquare.Tasks.T01.Quadratic

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

theorem chart_axis_unit (t : ℝ) : normSq (chartAxis t) = 1 := by
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  dsimp [normSq, dot, chartAxis]
  field_simp [hd]
  ring

/-- A square centered at the actual center, but with a fixed rational chart
    angle. This is the reference frame used by static median facets. -/
def referenceSquare (actual : UnitSquare) (angle : ℚ) : UnitSquare where
  center := actual.center
  axis := chartAxis (angle : ℝ)
  axis_unit := chart_axis_unit _

def referenceCorner (angle h sx sy : ℚ) : QPoint :=
  let ux := (1 - angle ^ 2) / (1 + angle ^ 2)
  let uy := 2 * angle / (1 + angle ^ 2)
  (sx * h * ux - sy * h * uy, sx * h * uy + sy * h * ux)

theorem reference_corner_eq (actual : UnitSquare) (angle h sx sy : ℚ) :
    fromLocalCoordinates (referenceSquare actual angle)
      (((sx * h : ℚ) : ℝ), ((sy * h : ℚ) : ℝ)) =
      actual.center + realPoint (referenceCorner angle h sx sy) := by
  apply Prod.ext <;>
    dsimp [fromLocalCoordinates, referenceSquare, referenceCorner,
      chartAxis, perp, realPoint] <;>
    push_cast <;> ring

theorem reference_corner_open_of_check (actual : UnitSquare)
    (angle h sx sy lo hi : ℚ) (t : ℝ)
    (hcheck : BaselineCoreVertexCheck (referenceCorner angle h sx sy) lo hi)
    (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ))
    (ha : actual.axis = chartAxis t) :
    OpenSquare actual
      (fromLocalCoordinates (referenceSquare actual angle)
        (((sx * h : ℚ) : ℝ), ((sy * h : ℚ) : ℝ))) := by
  rw [reference_corner_eq]
  exact baseline_core_vertex_check_sound actual
    (referenceCorner angle h sx sy) lo hi hcheck t hlo hhi ha

/-- Four strict corner checks carry a closed rectangle in a reference frame
    into the open interior of a possibly rotated square. -/
theorem reference_core_point_open (reference actual : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h)
    (hpp : OpenSquare actual (fromLocalCoordinates reference (h,h)))
    (hpn : OpenSquare actual (fromLocalCoordinates reference (h,-h)))
    (hnp : OpenSquare actual (fromLocalCoordinates reference (-h,h)))
    (hnn : OpenSquare actual (fromLocalCoordinates reference (-h,-h)))
    (v : Point) (hx : |v.1| ≤ h) (hy : |v.2| ≤ h) :
    OpenSquare actual (fromLocalCoordinates reference v) := by
  let ends : Set ℝ := {-h, h}
  have hspan : -h ≤ h := by linarith
  have hxrange : -h ≤ v.1 ∧ v.1 ≤ h := abs_le.mp hx
  have hyrange : -h ≤ v.2 ∧ v.2 ≤ h := abs_le.mp hy
  have hxhull : v.1 ∈ convexHull ℝ ends := by
    change v.1 ∈ convexHull ℝ ({-h,h} : Set ℝ)
    rw [convexHull_pair, segment_eq_Icc hspan]
    exact hxrange
  have hyhull : v.2 ∈ convexHull ℝ ends := by
    change v.2 ∈ convexHull ℝ ({-h,h} : Set ℝ)
    rw [convexHull_pair, segment_eq_Icc hspan]
    exact hyrange
  have hvhull : v ∈ convexHull ℝ (ends ×ˢ ends) := by
    rw [convexHull_prod]
    exact ⟨hxhull, hyhull⟩
  have hcorners : ends ×ˢ ends ⊆
      (fromLocalAffineMap reference) ⁻¹' {p | OpenSquare actual p} := by
    intro w hw
    rcases w with ⟨wx,wy⟩
    obtain ⟨hwx,hwy⟩ := hw
    change wx ∈ ({-h,h} : Set ℝ) at hwx
    change wy ∈ ({-h,h} : Set ℝ) at hwy
    change OpenSquare actual (fromLocalCoordinates reference (wx,wy))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwx hwy
    rcases hwx with hx' | hx' <;> rcases hwy with hy' | hy' <;>
      subst wx <;> subst wy
    · exact hnn
    · exact hnp
    · exact hpn
    · exact hpp
  have hpre : Convex ℝ
      ((fromLocalAffineMap reference) ⁻¹' {p | OpenSquare actual p}) :=
    (openSquare_convex actual).affine_preimage (fromLocalAffineMap reference)
  exact (convexHull_min hcorners hpre) hvhull

/-- Canonical median bounds place every selected subset hull through the
    closed half-width `h` rectangle in a fixed reference frame. -/
theorem fixed_core_subset_capture_of_canonical
    (sites : Finset QPoint) (pairs : Finset (QPoint × QPoint))
    (k : ℕ) (reference : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h) (hk : 0 < k)
    (hcover : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      (a,b) ∈ pairs ∨ (b,a) ∈ pairs)
    (haxes : ∀ axis ∈ ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      LocalMedianBound sites k reference h axis)
    (hpairs : ∀ ab ∈ pairs,
      LocalMedianBound sites k reference h
        (pairPerp reference ab.1 ab.2) ∧
      LocalMedianBound sites k reference h
        (negPoint (pairPerp reference ab.1 ab.2)))
    (subset : Finset QPoint) (hsubset : subset ⊆ sites)
    (hcard : subset.card = k) :
    ∃ p ∈ rationalHull subset.toList,
      |localX reference p| ≤ h ∧ |localY reference p| ≤ h := by
  classical
  let localSites := subset.image (fun p => localCoordinates reference (realPoint p))
  have hsubne : subset.Nonempty :=
    Finset.card_pos.mp (by simpa [hcard] using hk)
  have hlocalne : localSites.Nonempty := hsubne.image _
  have hpairsAll : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      LocalMedianBound sites k reference h (pairPerp reference a b) ∧
      LocalMedianBound sites k reference h
        (negPoint (pairPerp reference a b)) := by
    intro a ha b hb hab
    rcases hcover a ha b hb hab with habpair | hbapair
    · exact hpairs (a,b) habpair
    · obtain ⟨hpos, hneg⟩ := hpairs (b,a) hbapair
      constructor
      · rw [neg_pair_perp_swap reference a b] at hneg
        exact hneg
      · rw [pair_perp_swap reference a b] at hpos
        exact hpos
  have hlocal : localSites ⊆
      sites.image (fun p => localCoordinates reference (realPoint p)) :=
    Finset.image_subset_image hsubset
  have hbreak : ∀ sx sy : ℝ,
      (sx = 1 ∨ sx = -1) → (sy = 1 ∨ sy = -1) →
      ∀ r ∈ affineBreakpoints (localSites.image (quadrantLine sx sy)),
        0 ≤ r → r ≤ 1 →
        ∃ p ∈ localSites,
          dot (quadrantNormal sx sy r) (0,0) ≤
            dot (quadrantNormal sx sy r) p + h := by
    intro sx sy hsx hsy r hr hr0 hr1
    have hlines : localSites.image (quadrantLine sx sy) ⊆
        (sites.image (fun p => localCoordinates reference (realPoint p))).image
          (quadrantLine sx sy) := Finset.image_subset_image hlocal
    have hrall := affineBreakpoints_mono hlines hr
    obtain ⟨bound, hmedian, hbound⟩ :=
      local_median_at_breakpoint_of_canonical sites k reference h
        haxes hpairsAll sx sy hsx hsy r hrall hr0 hr1
    obtain ⟨p, hp, hprojection⟩ :=
      median_lower_bound_hits_subset sites subset k
        (localProjection reference (quadrantNormal sx sy r))
        bound hmedian hsubset hcard
    have hnorm := quadrant_normal_l1 sx sy r hsx hsy hr0 hr1
    rw [hnorm] at hbound
    refine ⟨localCoordinates reference (realPoint p),
      Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    dsimp [localProjection, localCoordinates, dot] at hprojection ⊢
    linarith
  obtain ⟨v, hv, hx, hy⟩ :=
    finite_normal_closed_square_capture localSites hlocalne h hh hbreak
  refine ⟨fromLocalCoordinates reference v,
    local_hull_preimage reference subset v hv, ?_, ?_⟩
  · change |(localCoordinates reference (fromLocalCoordinates reference v)).1| ≤ h
    rw [from_local_coordinates_right]
    exact hx
  · change |(localCoordinates reference (fromLocalCoordinates reference v)).2| ≤ h
    rw [from_local_coordinates_right]
    exact hy

/-- A fixed rational reference core can prove majority capture throughout a
    whole angle interval using only four moving core-corner checks. -/
theorem majority_capture_of_fixed_core
    (sites : Finset QPoint) (pairs : Finset (QPoint × QPoint))
    (k : ℕ) (reference actual : UnitSquare) (h : ℝ)
    (hh : 0 ≤ h) (hk : 0 < k)
    (hcover : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      (a,b) ∈ pairs ∨ (b,a) ∈ pairs)
    (haxes : ∀ axis ∈ ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      LocalMedianBound sites k reference h axis)
    (hpairs : ∀ ab ∈ pairs,
      LocalMedianBound sites k reference h
        (pairPerp reference ab.1 ab.2) ∧
      LocalMedianBound sites k reference h
        (negPoint (pairPerp reference ab.1 ab.2)))
    (hpp : OpenSquare actual (fromLocalCoordinates reference (h,h)))
    (hpn : OpenSquare actual (fromLocalCoordinates reference (h,-h)))
    (hnp : OpenSquare actual (fromLocalCoordinates reference (-h,h)))
    (hnn : OpenSquare actual (fromLocalCoordinates reference (-h,-h))) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k actual := by
  classical
  intro subset hmem
  obtain ⟨hsubset,hcard⟩ := Finset.mem_powersetCard.mp hmem
  obtain ⟨p,hp,hx,hy⟩ :=
    fixed_core_subset_capture_of_canonical sites pairs k reference h
      hh hk hcover haxes hpairs subset hsubset hcard
  refine ⟨p,hp,?_⟩
  rw [← from_local_coordinates_left reference p]
  apply reference_core_point_open reference actual h hh hpp hpn hnp hnn
  · exact hx
  · exact hy

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.reference_core_point_open
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.fixed_core_subset_capture_of_canonical
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.majority_capture_of_fixed_core
