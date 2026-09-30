import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFixedCore
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSupportFacet

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

def rationalPerp (v : QPoint) : QPoint := (-v.2,v.1)
def rationalNeg (v : QPoint) : QPoint := (-v.1,-v.2)

def referenceAxisQ (angle : ℚ) : QPoint :=
  ((1 - angle ^ 2) / (1 + angle ^ 2),
    2 * angle / (1 + angle ^ 2))

theorem reference_square_axis (actual : UnitSquare) (angle : ℚ) :
    (referenceSquare actual angle).axis = realPoint (referenceAxisQ angle) := by
  apply Prod.ext <;>
    dsimp [referenceSquare, referenceAxisQ, realPoint, chartAxis] <;>
    push_cast <;> rfl

theorem reference_axisQ_unit (angle : ℚ) :
    rationalDot (referenceAxisQ angle) (referenceAxisQ angle) = 1 := by
  have hd : 1 + angle ^ 2 ≠ 0 := ne_of_gt (by positivity)
  dsimp [rationalDot, referenceAxisQ]
  field_simp [hd] <;> ring

def localNormalQ (axis normal : QPoint) : QPoint :=
  (rationalDot normal axis, rationalDot normal (rationalPerp axis))

theorem local_normal_axis (axis : QPoint)
    (hunit : rationalDot axis axis = 1) :
    localNormalQ axis axis = (1,0) := by
  apply Prod.ext
  · exact hunit
  · dsimp [localNormalQ, rationalDot, rationalPerp]
    ring

theorem local_normal_perp (axis : QPoint)
    (hunit : rationalDot axis axis = 1) :
    localNormalQ axis (rationalPerp axis) = (0,1) := by
  apply Prod.ext
  · dsimp [localNormalQ, rationalDot, rationalPerp]
    ring
  · simpa [localNormalQ, rationalDot, rationalPerp, add_comm] using hunit

theorem local_normal_neg (axis normal : QPoint) :
    localNormalQ axis (rationalNeg normal) =
      rationalNeg (localNormalQ axis normal) := by
  apply Prod.ext <;>
    dsimp [localNormalQ, rationalDot, rationalPerp, rationalNeg] <;>
    ring

def pairWorldQ (a b : QPoint) : QPoint :=
  (b.2 - a.2, a.1 - b.1)

theorem local_normal_pair (reference : UnitSquare)
    (axis a b : QPoint) (ha : reference.axis = realPoint axis) :
    realPoint (localNormalQ axis (pairWorldQ a b)) =
      pairPerp reference a b := by
  apply Prod.ext <;>
    dsimp [localNormalQ, rationalDot, rationalPerp, pairWorldQ,
      pairPerp, pairDX, pairDY, realPoint, localX, localY,
      dot, perp] <;>
    rw [ha] <;>
    dsimp [realPoint] <;>
    push_cast <;>
    ring

theorem real_rational_neg (v : QPoint) :
    realPoint (rationalNeg v) = negPoint (realPoint v) := by
  apply Prod.ext <;> simp [realPoint, rationalNeg, negPoint]

def rationalCoreSupport (axis normal : QPoint) : ℚ :=
  |(localNormalQ axis normal).1| + |(localNormalQ axis normal).2|

/-- A finite rational check for a static median target facet. The chosen
    threshold is recovered from the facet bound and core support. -/
def FixedMedianFacetCheck (sites : Finset QPoint) (k : ℕ)
    (axis : QPoint) (h : ℚ) (target : Polygon) (normal : QPoint) : Prop :=
  ∃ facet ∈ target,
    facet.a = normal.1 ∧ facet.b = normal.2 ∧
    MedianLowerBound sites k (rationalDot normal)
      (facet.c - h * rationalCoreSupport axis normal)

instance (sites : Finset QPoint) (k : ℕ)
    (axis : QPoint) (h : ℚ) (target : Polygon) (normal : QPoint) :
    Decidable (FixedMedianFacetCheck sites k axis h target normal) := by
  change Decidable (∃ facet, facet ∈ target ∧
    (facet.a = normal.1 ∧ facet.b = normal.2 ∧
      MedianLowerBound sites k (rationalDot normal)
        (facet.c - h * rationalCoreSupport axis normal)))
  letI (facet : Halfplane) : Decidable
      (MedianLowerBound sites k (rationalDot normal)
        (facet.c - h * rationalCoreSupport axis normal)) := by
    unfold MedianLowerBound
    infer_instance
  exact List.decidableBEx _ target

theorem real_rational_dot (normal site : QPoint) :
    dot (realPoint normal) (realPoint site) = (rationalDot normal site : ℝ) := by
  norm_num [dot, realPoint, rationalDot]

theorem local_projection_of_world_normal
    (reference : UnitSquare) (axis normal : QPoint)
    (ha : reference.axis = realPoint axis) (site : QPoint) :
    localProjection reference (realPoint (localNormalQ axis normal)) site =
      dot (realPoint normal) (realPoint site) -
        dot (realPoint normal) reference.center := by
  have hrec := coordinate_reconstruction (realPoint normal)
    reference.axis reference.axis_unit
  have hx := congrArg Prod.fst hrec
  have hy := congrArg Prod.snd hrec
  dsimp [localProjection, localNormalQ, rationalDot, realPoint,
    localX, localY, dot, perp, rationalPerp] at hx hy ⊢
  rw [ha] at hx hy ⊢
  dsimp [realPoint] at hx hy ⊢
  push_cast at hx hy ⊢
  linear_combination
    -((site.1 : ℝ) - reference.center.1) * hx -
    ((site.2 : ℝ) - reference.center.2) * hy

/-- A checked rational facet gives the real local median support bound for
    the corresponding normal in a fixed rational reference frame. -/
theorem fixed_median_facet_sound
    (sites : Finset QPoint) (k : ℕ) (reference : UnitSquare)
    (axis : QPoint) (h : ℚ) (target : Polygon) (normal : QPoint)
    (ha : reference.axis = realPoint axis)
    (hcenter : reference.center ∈ target.carrier)
    (hcheck : FixedMedianFacetCheck sites k axis h target normal) :
    LocalMedianBound sites k reference (h : ℝ)
      (realPoint (localNormalQ axis normal)) := by
  obtain ⟨facet,hfacet,ha',hb',hmedian⟩ := hcheck
  let bound : ℚ := facet.c - h * rationalCoreSupport axis normal
  let projection : QPoint → ℝ :=
    fun p => dot (realPoint normal) (realPoint p)
  have hmedianReal : MedianLowerBound sites k projection (bound : ℝ) := by
    unfold MedianLowerBound at hmedian ⊢
    have hfilter : sites.filter (fun p => projection p < (bound : ℝ)) =
        sites.filter (fun p => rationalDot normal p < bound) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp,hlt⟩
        refine ⟨hp, ?_⟩
        dsimp [projection] at hlt
        rw [real_rational_dot] at hlt
        exact_mod_cast hlt
      · rintro ⟨hp,hlt⟩
        refine ⟨hp, ?_⟩
        dsimp [projection]
        rw [real_rational_dot]
        exact_mod_cast hlt
    rw [hfilter]
    exact hmedian
  let centerValue := dot (realPoint normal) reference.center
  refine ⟨(bound : ℝ) - centerValue, ?_, ?_⟩
  · unfold MedianLowerBound at hmedianReal ⊢
    have hfilter :
        sites.filter (fun p =>
          localProjection reference (realPoint (localNormalQ axis normal)) p <
            (bound : ℝ) - centerValue) =
        sites.filter (fun p => projection p < (bound : ℝ)) := by
      ext p
      simp only [Finset.mem_filter]
      rw [local_projection_of_world_normal reference axis normal ha]
      dsimp [projection, centerValue]
      simp only [sub_lt_sub_iff_right]
    rw [hfilter]
    exact hmedianReal
  · have hf := hcenter facet hfacet
    have hsup :
        (rationalCoreSupport axis normal : ℝ) =
          |(realPoint (localNormalQ axis normal)).1| +
            |(realPoint (localNormalQ axis normal)).2| := by
      simp [rationalCoreSupport, realPoint]
    have hc : centerValue ≤ (facet.c : ℝ) := by
      dsimp [Halfplane.contains, centerValue, dot, realPoint] at hf ⊢
      rw [ha', hb'] at hf
      exact hf
    have hb : (bound : ℝ) = (facet.c : ℝ) -
        (h : ℝ) * (rationalCoreSupport axis normal : ℝ) := by
      simp [bound]
    rw [← hsup]
    linarith

/-- The static 24-facet producer interface for a five-site feature. The
    finite checks are rational; only the four strict core corners depend on
    the actual square angle. The pair roster needs one orientation of each
    unordered pair. -/
theorem fixed_core_majority_of_target
    (sites : Finset QPoint) (pairs : Finset (QPoint × QPoint))
    (k : ℕ) (actual : UnitSquare)
    (angle half lo hi : ℚ) (t : ℝ) (target : Polygon)
    (hh : 0 ≤ half) (hk : 0 < k)
    (htlo : (lo : ℝ) ≤ t) (hthi : t ≤ (hi : ℝ))
    (ha : actual.axis = chartAxis t)
    (hcenter : actual.center ∈ target.carrier)
    (hcover : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      (a,b) ∈ pairs ∨ (b,a) ∈ pairs)
    (haxes : ∀ n ∈ ([referenceAxisQ angle,
        rationalNeg (referenceAxisQ angle),
        rationalPerp (referenceAxisQ angle),
        rationalNeg (rationalPerp (referenceAxisQ angle))] : List QPoint),
      FixedMedianFacetCheck sites k (referenceAxisQ angle) half target n)
    (hpairs : ∀ ab ∈ pairs,
      FixedMedianFacetCheck sites k (referenceAxisQ angle) half target
        (pairWorldQ ab.1 ab.2) ∧
      FixedMedianFacetCheck sites k (referenceAxisQ angle) half target
        (rationalNeg (pairWorldQ ab.1 ab.2)))
    (hpp : BaselineCoreVertexCheck (referenceCorner angle half 1 1) lo hi)
    (hpn : BaselineCoreVertexCheck (referenceCorner angle half 1 (-1)) lo hi)
    (hnp : BaselineCoreVertexCheck (referenceCorner angle half (-1) 1) lo hi)
    (hnn : BaselineCoreVertexCheck (referenceCorner angle half (-1) (-1)) lo hi) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k actual := by
  let reference := referenceSquare actual angle
  let axis := referenceAxisQ angle
  have hrefaxis : reference.axis = realPoint axis :=
    reference_square_axis actual angle
  have hrefcenter : reference.center ∈ target.carrier := hcenter
  have hunit : rationalDot axis axis = 1 := reference_axisQ_unit angle
  have hmedianAxes : ∀ normal ∈
      ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      LocalMedianBound sites k reference (half : ℝ) normal := by
    intro normal hnormal
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnormal
    rcases hnormal with rfl | rfl | rfl | rfl
    · have hc := haxes axis (by simp [axis])
      have hm := fixed_median_facet_sound sites k reference axis half target
        axis hrefaxis hrefcenter hc
      simpa [local_normal_axis axis hunit, realPoint] using hm
    · have hc := haxes (rationalNeg axis) (by simp [axis])
      have hm := fixed_median_facet_sound sites k reference axis half target
        (rationalNeg axis) hrefaxis hrefcenter hc
      have heq : realPoint (localNormalQ axis (rationalNeg axis)) =
          (-1,0) := by
        rw [local_normal_neg, local_normal_axis axis hunit]
        norm_num [realPoint, rationalNeg]
      rw [heq] at hm
      exact hm
    · have hc := haxes (rationalPerp axis) (by simp [axis])
      have hm := fixed_median_facet_sound sites k reference axis half target
        (rationalPerp axis) hrefaxis hrefcenter hc
      simpa [local_normal_perp axis hunit, realPoint] using hm
    · have hc := haxes (rationalNeg (rationalPerp axis)) (by simp [axis])
      have hm := fixed_median_facet_sound sites k reference axis half target
        (rationalNeg (rationalPerp axis)) hrefaxis hrefcenter hc
      have heq : realPoint (localNormalQ axis
          (rationalNeg (rationalPerp axis))) = (0,-1) := by
        rw [local_normal_neg, local_normal_perp axis hunit]
        norm_num [realPoint, rationalNeg]
      rw [heq] at hm
      exact hm
  have hmedianPairs : ∀ ab ∈ pairs,
      LocalMedianBound sites k reference (half : ℝ)
        (pairPerp reference ab.1 ab.2) ∧
      LocalMedianBound sites k reference (half : ℝ)
        (negPoint (pairPerp reference ab.1 ab.2)) := by
    intro ab hab
    obtain ⟨hcp,hcn⟩ := hpairs ab hab
    have hmp := fixed_median_facet_sound sites k reference axis half target
      (pairWorldQ ab.1 ab.2) hrefaxis hrefcenter hcp
    have hmn := fixed_median_facet_sound sites k reference axis half target
      (rationalNeg (pairWorldQ ab.1 ab.2)) hrefaxis hrefcenter hcn
    have heq := local_normal_pair reference axis ab.1 ab.2 hrefaxis
    constructor
    · simpa only [heq] using hmp
    · rw [local_normal_neg, real_rational_neg, heq] at hmn
      exact hmn
  have hcornerpp : OpenSquare actual
      (fromLocalCoordinates reference ((half : ℝ),(half : ℝ))) := by
    simpa [reference] using
      reference_corner_open_of_check actual angle half 1 1 lo hi t
        hpp htlo hthi ha
  have hcornerpn : OpenSquare actual
      (fromLocalCoordinates reference ((half : ℝ),-(half : ℝ))) := by
    simpa [reference] using
      reference_corner_open_of_check actual angle half 1 (-1) lo hi t
        hpn htlo hthi ha
  have hcornernp : OpenSquare actual
      (fromLocalCoordinates reference (-(half : ℝ),(half : ℝ))) := by
    simpa [reference] using
      reference_corner_open_of_check actual angle half (-1) 1 lo hi t
        hnp htlo hthi ha
  have hcornernn : OpenSquare actual
      (fromLocalCoordinates reference (-(half : ℝ),-(half : ℝ))) := by
    simpa [reference] using
      reference_corner_open_of_check actual angle half (-1) (-1) lo hi t
        hnn htlo hthi ha
  exact majority_capture_of_fixed_core sites pairs k reference actual
    (half : ℝ) (by exact_mod_cast hh) hk hcover hmedianAxes hmedianPairs
    hcornerpp hcornerpn hcornernp hcornernn

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.fixed_median_facet_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.fixed_core_majority_of_target
