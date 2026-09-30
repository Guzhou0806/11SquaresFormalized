import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node006_checked :
    node006.Check nodeSource006 targets (161/4096) (309/2048) := by
  norm_num [SymbolicCoverCertificate.Check, SymbolicPolygonImplicationCheck,
    SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul, quarticAdd,
    quarticSub, List.getD, node006, nodeSource006, targets, target00, target01, target02, splitFacet000, splitFacet001, splitFacet002, source, SymbolicFacet.flip, SymbolicQuadratic.neg]

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001
