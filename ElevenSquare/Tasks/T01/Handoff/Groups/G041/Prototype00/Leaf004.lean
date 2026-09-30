import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets 0 (1/512) := by
  norm_num [
    SymbolicCoverCertificate.Check,
    SymbolicPolygonImplicationCheck,
    SymbolicFarkasWitness.Check,
    SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck,
    Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn,
    Quartic.toBernstein,
    Quartic.shift,
    SymbolicQuadratic.quartic,
    SymbolicQuadratic.mul,
    quarticAdd,
    quarticSub,
    List.getD,
    node004,
    nodeSource004,
    targets,
    source,
    Field03SymbolicCell04Regime000.source,
    SymbolicFacet.flip,
    SymbolicQuadratic.neg,
    target00,
    target01,
    target02,
    target03,
    target04,
    splitFacet000,
    splitFacet001,
    splitFacet002]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00
