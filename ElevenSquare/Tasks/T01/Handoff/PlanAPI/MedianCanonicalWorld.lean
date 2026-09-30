import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianCanonicalNormals
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianWorldBridge

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- Symbolic producer interface for arbitrary-size odd features: four axis
    median facets and both pair-perpendicular facets for each site pair.
    The same facets capture every selected `k`-subset. -/
theorem symbolic_majority_of_axes_and_pairs
    (sites : Finset QPoint) (k : ℕ)
    (q : UnitSquare) (t h : ℝ)
    (hwidth : 0 ≤ h ∧ h < 1 / 2) (hk : 0 < k)
    (ha : q.axis = chartAxis t)
    (target : List SymbolicFacet)
    (hcontains : SymbolicPolygonContains target t q.center)
    (haxes : ∀ axis ∈ ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      SymbolicMedianFacetWitness sites k q t h axis target)
    (hpairs : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      SymbolicMedianFacetWitness sites k q t h (pairPerp q a b) target ∧
      SymbolicMedianFacetWitness sites k q t h
        (negPoint (pairPerp q a b)) target) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k q := by
  apply majority_capture_of_axes_and_pairs sites k q h
    hwidth.1 hwidth.2 hk
  · intro axis haxis
    exact symbolic_median_facet_witness_sound sites k q t h ha axis target
      hcontains (haxes axis haxis)
  · intro a haa b hbb hab
    exact ⟨symbolic_median_facet_witness_sound sites k q t h ha
        (pairPerp q a b) target hcontains (hpairs a haa b hbb hab).1,
      symbolic_median_facet_witness_sound sites k q t h ha
        (negPoint (pairPerp q a b)) target hcontains
        (hpairs a haa b hbb hab).2⟩

/-- A concrete producer can list one orientation of each unordered pair.
    For five distinct sites this is ten pair entries and twenty facet
    witnesses, in addition to the four axes. -/
theorem symbolic_majority_of_pair_cover
    (sites : Finset QPoint) (pairs : Finset (QPoint × QPoint))
    (k : ℕ) (q : UnitSquare) (t h : ℝ)
    (hwidth : 0 ≤ h ∧ h < 1 / 2) (hk : 0 < k)
    (ha : q.axis = chartAxis t)
    (target : List SymbolicFacet)
    (hcontains : SymbolicPolygonContains target t q.center)
    (hcover : ∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
      (a,b) ∈ pairs ∨ (b,a) ∈ pairs)
    (haxes : ∀ axis ∈ ([(1,0), (-1,0), (0,1), (0,-1)] : List Point),
      SymbolicMedianFacetWitness sites k q t h axis target)
    (hpairs : ∀ ab ∈ pairs,
      SymbolicMedianFacetWitness sites k q t h
        (pairPerp q ab.1 ab.2) target ∧
      SymbolicMedianFacetWitness sites k q t h
        (negPoint (pairPerp q ab.1 ab.2)) target) :
    ElevenSquare.Tasks.T01.BaselineMajorityCapture sites k q := by
  apply majority_capture_of_pair_cover sites pairs k q h
    hwidth.1 hwidth.2 hk hcover
  · intro axis haxis
    exact symbolic_median_facet_witness_sound sites k q t h ha axis target
      hcontains (haxes axis haxis)
  · intro ab hab
    exact ⟨symbolic_median_facet_witness_sound sites k q t h ha
        (pairPerp q ab.1 ab.2) target hcontains (hpairs ab hab).1,
      symbolic_median_facet_witness_sound sites k q t h ha
        (negPoint (pairPerp q ab.1 ab.2)) target hcontains
        (hpairs ab hab).2⟩

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_majority_of_axes_and_pairs
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_majority_of_pair_cover
