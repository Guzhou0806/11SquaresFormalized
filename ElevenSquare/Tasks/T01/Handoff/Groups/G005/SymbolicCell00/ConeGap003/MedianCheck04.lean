import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.MedianData

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem medCert04_checked :
    (medCert04).Check G005.featureB 2 target half left right := by
  norm_num [MedianFacetCertificate.Check, MedianFacetCertificate.expectedBound,
    MedianDirection.worldA, MedianDirection.worldB, MedianDirection.supportU,
    MedianDirection.supportV, MedianDirection.projection, SymbolicQuadratic.add,
    SymbolicQuadratic.sub, SymbolicQuadratic.neg, SymbolicQuadratic.scale,
    SymbolicQuadratic.scaleByChart, SymbolicQuadratic.quartic,
    chartA, chartB, chartD, pairNX, pairNY,
    Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.toBernstein,
    Quartic.shift, List.getD,
    medCert04, G005.featureB, G005.site02, G005.site06, G005.site07,
    G005.physicalToUnit, target, facet00, facet01, facet02, facet03, facet04, facet05, facet06, facet07, facet08, facet09,
    half, left, right]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.medCert04_checked
