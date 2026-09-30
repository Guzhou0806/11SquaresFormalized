import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFiniteCapture
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianWorldBridge

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- A symbolic target containing one checked lower-median facet for each
    finite breakpoint normal captures every `k`-subset of an arbitrary finite
    feature. This includes five- and seven-site features. -/
theorem symbolic_finite_median_target_majority
    (sites : Finset QPoint) (k : ℕ)
    (q : UnitSquare) (t h : ℝ)
    (hwidth : 0 ≤ h ∧ h < 1 / 2) (hk : 0 < k)
    (ha : q.axis = chartAxis t)
    (target : List SymbolicFacet)
    (hcontains : SymbolicPolygonContains target t q.center)
    (hw : ∀ normal ∈ medianBreakpointNormals sites q,
      SymbolicMedianFacetWitness sites k q t h normal target) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k q := by
  apply majority_capture_of_finite_median_normals sites k q h
    hwidth.1 hwidth.2 hk
  intro normal hn
  exact symbolic_median_facet_witness_sound sites k q t h ha normal target
    hcontains (hw normal hn)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_finite_median_target_majority
