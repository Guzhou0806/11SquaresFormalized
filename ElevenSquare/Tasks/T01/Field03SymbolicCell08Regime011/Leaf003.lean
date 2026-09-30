import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node003_checked :
    node003.Check nodeSource003 targets (2847/4096) (751/1024) := by
  norm_num [SymbolicCoverCertificate.Check, SymbolicPolygonImplicationCheck,
    SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul, quarticAdd,
    quarticSub, List.getD, node003, nodeSource003, targets, target00, target01, target02, splitFacet000, splitFacet001, source, SymbolicFacet.flip, SymbolicQuadratic.neg]

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011
