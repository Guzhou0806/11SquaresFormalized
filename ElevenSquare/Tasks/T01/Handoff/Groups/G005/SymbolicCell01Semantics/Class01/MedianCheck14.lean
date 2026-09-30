import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class01.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem medCert14_checked :
    (medCert14).Check G005.featureA 3 target half left right := by
  norm_num [MedianFacetCertificate.Check, MedianFacetCertificate.expectedBound,
    MedianDirection.worldA, MedianDirection.worldB, MedianDirection.supportU,
    MedianDirection.supportV, MedianDirection.projection, SymbolicQuadratic.add,
    SymbolicQuadratic.sub, SymbolicQuadratic.neg, SymbolicQuadratic.scale,
    SymbolicQuadratic.scaleByChart, SymbolicQuadratic.quartic,
    chartA, chartB, chartD, pairNX, pairNY,
    Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.toBernstein,
    Quartic.shift, List.getD,
    medCert14, G005.featureA, G005.site00, G005.site01,
    G005.site03, G005.site04, G005.site05, G005.physicalToUnit,
    target, facet00, facet01, facet02, facet03, facet04, facet05, facet06, facet07, facet08, facet09, facet10, facet11, facet12, facet13, facet14, facet15, facet16, facet17, facet18, facet19, facet20, facet21, facet22, facet23,
    half, left, right]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class01

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class01.medCert14_checked
