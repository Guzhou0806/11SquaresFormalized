import ElevenSquare.Tasks.T01.Handoff.PlanAPI.G004PairMedianCache

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- Once the angle-independent median order is known, a fixed-window pair
facet only has to match its normal and its exact support bound. -/
theorem fixed_median_facet_of_cached_lower
    (sites : Finset QPoint) (k : ℕ) (axis : QPoint)
    (half : ℚ) (target : Polygon) (normal medianSite : QPoint)
    (facet : Halfplane) (hfacet : facet ∈ target)
    (ha : facet.a = normal.1) (hb : facet.b = normal.2)
    (hbound : facet.c - half * rationalCoreSupport axis normal =
      rationalDot normal medianSite)
    (hmedian : MedianLowerBound sites k (rationalDot normal)
      (rationalDot normal medianSite)) :
    FixedMedianFacetCheck sites k axis half target normal := by
  refine ⟨facet, hfacet, ha, hb, ?_⟩
  rw [hbound]
  exact hmedian

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.fixed_median_facet_of_cached_lower
