import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node005_checked :
    node005.Check nodeSource005 targets (717/2048) (897/2048) := by
  norm_num [SymbolicCoverCertificate.Check, SymbolicPolygonImplicationCheck,
    SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul, quarticAdd,
    quarticSub, List.getD, node005, nodeSource005, targets, target00, target01, target02, target03, splitFacet000, splitFacet001, splitFacet002, source, SymbolicFacet.flip, SymbolicQuadratic.neg]

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007
