import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSegmentCapture
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCover

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

def chartDenom (t : ℝ) : ℝ := 1 + t ^ 2

def chartNumeratorNormal (t : ℝ) (normal : Point) : Point :=
  (normal.1 * (1 - t ^ 2) - normal.2 * (2 * t),
   normal.1 * (2 * t) + normal.2 * (1 - t ^ 2))

theorem chartDenom_pos (t : ℝ) : 0 < chartDenom t := by
  dsimp [chartDenom]
  positivity

/-- A local projection, after clearing the chart denominator, is an affine
    world-coordinate projection. The center translation is explicit. -/
theorem local_projection_chart_identity
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (normal : Point) (site : QPoint) :
    chartDenom t * localProjection q normal site =
      dot (chartNumeratorNormal t normal) (realPoint site) -
        dot (chartNumeratorNormal t normal) q.center := by
  dsimp [chartDenom, localProjection, chartNumeratorNormal,
    localX, localY, dot, perp, realPoint]
  rw [ha]
  dsimp [chartAxis]
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + t ^ 2)
  field_simp [hd]
  ring

/-- World-coordinate median bounds transfer to the local directions used by
    segment capture. The source polygon may prove the center bound through a
    symbolic facet; order of the three site projections is checked separately. -/
theorem local_median_of_world_support
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (t h : ℝ)
    (ha : q.axis = chartAxis t) (normal : Point) (bound : ℝ)
    (hmedian : MedianLowerBound sites k
      (fun p => dot (chartNumeratorNormal t normal) (realPoint p)) bound)
    (hcenter : dot (chartNumeratorNormal t normal) q.center ≤
      bound + h * chartDenom t * (|normal.1| + |normal.2|)) :
    LocalMedianBound sites k q h normal := by
  let worldNormal := chartNumeratorNormal t normal
  let worldCenter := dot worldNormal q.center
  let localBound := (bound - worldCenter) / chartDenom t
  have hd := chartDenom_pos t
  have hlt (p : QPoint) :
      localProjection q normal p < localBound ↔
      dot worldNormal (realPoint p) < bound := by
    have he := local_projection_chart_identity q t ha normal p
    change chartDenom t * localProjection q normal p =
      dot worldNormal (realPoint p) - worldCenter at he
    dsimp [localBound]
    rw [lt_div_iff' hd]
    rw [he]
    constructor <;> intro hh <;> linarith
  have hfilter : sites.filter (fun p => localProjection q normal p < localBound) =
      sites.filter (fun p => dot worldNormal (realPoint p) < bound) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hproj⟩
      exact ⟨hp, (hlt p).mp hproj⟩
    · rintro ⟨hp, hproj⟩
      exact ⟨hp, (hlt p).mpr hproj⟩
  refine ⟨localBound, ?_, ?_⟩
  · unfold MedianLowerBound at hmedian ⊢
    rw [hfilter]
    exact hmedian
  · have hnum : 0 ≤ bound - worldCenter +
        h * chartDenom t * (|normal.1| + |normal.2|) := by
      dsimp [worldCenter, worldNormal] at hcenter ⊢
      linarith
    have hdiv := div_nonneg hnum hd.le
    dsimp [localBound]
    convert hdiv using 1
    field_simp [ne_of_gt hd]
    ring

/-- An evaluated symbolic TRUE facet may be a positive multiple of the
    world-coordinate median inequality. Moving chart-axis facets use scale
    one; fixed pair-normal facets may use scale `1+t²`. -/
theorem local_median_of_symbolic_facet
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (t h : ℝ)
    (ha : q.axis = chartAxis t) (normal : Point) (bound : ℝ)
    (facet : SymbolicFacet) (scale : ℝ)
    (hscale : 0 < scale)
    (hax : facet.a.eval t = scale * (chartNumeratorNormal t normal).1)
    (hby : facet.b.eval t = scale * (chartNumeratorNormal t normal).2)
    (hct : facet.c.eval t ≤ scale *
      (bound + h * chartDenom t * (|normal.1| + |normal.2|)))
    (hmedian : MedianLowerBound sites k
      (fun p => dot (chartNumeratorNormal t normal) (realPoint p)) bound)
    (hcenter : facet.contains t q.center) :
    LocalMedianBound sites k q h normal := by
  have hw : dot (chartNumeratorNormal t normal) q.center ≤
      bound + h * chartDenom t * (|normal.1| + |normal.2|) := by
    apply (mul_le_mul_left hscale).mp
    calc
      scale * dot (chartNumeratorNormal t normal) q.center =
          facet.a.eval t * q.center.1 + facet.b.eval t * q.center.2 := by
            rw [hax, hby]
            dsimp [dot]
            ring
      _ ≤ facet.c.eval t := hcenter
      _ ≤ scale * (bound + h * chartDenom t *
        (|normal.1| + |normal.2|)) := hct
  exact local_median_of_world_support sites k q t h ha normal bound hmedian hw

/-- One evaluated symbolic facet supplies a lower-median inequality in a
    specified local normal. The world projection ordering is the only
    combinatorial condition. -/
def SymbolicMedianFacetWitness (sites : Finset QPoint) (k : ℕ)
    (q : UnitSquare) (t h : ℝ) (normal : Point)
    (target : List SymbolicFacet) : Prop :=
  ∃ facet ∈ target, ∃ scale bound : ℝ,
    0 < scale ∧
    facet.a.eval t = scale * (chartNumeratorNormal t normal).1 ∧
    facet.b.eval t = scale * (chartNumeratorNormal t normal).2 ∧
    facet.c.eval t ≤ scale *
      (bound + h * chartDenom t * (|normal.1| + |normal.2|)) ∧
    MedianLowerBound sites k
      (fun p => dot (chartNumeratorNormal t normal) (realPoint p)) bound

theorem symbolic_median_facet_witness_sound
    (sites : Finset QPoint) (k : ℕ) (q : UnitSquare) (t h : ℝ)
    (ha : q.axis = chartAxis t) (normal : Point)
    (target : List SymbolicFacet)
    (hcontains : SymbolicPolygonContains target t q.center)
    (hw : SymbolicMedianFacetWitness sites k q t h normal target) :
    LocalMedianBound sites k q h normal := by
  obtain ⟨facet, hfacet, scale, bound, hscale, hax, hby, hct, hmedian⟩ := hw
  exact local_median_of_symbolic_facet sites k q t h ha normal bound facet scale
    hscale hax hby hct hmedian (hcontains facet hfacet)

/-- A ten-facet symbolic median target implies strict majority capture for
    the three-point feature. A producer only needs to prove one world-facet
    witness for each normal over its rational angle interval. -/
theorem symbolic_triple_median_target_majority
    (a b c : QPoint) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (q : UnitSquare) (t h : ℝ) (hwidth : 0 ≤ h ∧ h < 1 / 2)
    (ha : q.axis = chartAxis t) (target : List SymbolicFacet)
    (hcontains : SymbolicPolygonContains target t q.center)
    (hw : ∀ normal ∈ tripleMedianNormals q a b c,
      SymbolicMedianFacetWitness ({a,b,c} : Finset QPoint) 2
        q t h normal target) :
    BaselineMajorityCapture {a,b,c} 2 q := by
  apply triple_majority_of_median_bounds a b c hab hac hbc q h
    hwidth.1 hwidth.2
  intro normal hn
  exact symbolic_median_facet_witness_sound _ _ q t h ha normal target
    hcontains (hw normal hn)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.local_median_of_world_support
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.local_median_of_symbolic_facet
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_triple_median_target_majority
