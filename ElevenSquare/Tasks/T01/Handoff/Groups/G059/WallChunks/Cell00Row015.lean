import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row015
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 503b5639d78fd3e2e81417c28b75fc1a3c9374c2ef1c858d0496444e2b5a0378,
    physical cell 0, archived interval [15/32, 1/2]. -/
def p0 : QPoint := ((250923565552390045307244760797429/214568800000000000000000000000000), (7/10))
def p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def p3 : QPoint := ((7/10), (5645488939092747991754459106829/4457675000000000000000000000000))
def p4 : QPoint := ((7/10), (7/10))
def vertices : List QPoint := [p0, p1, p2, p3, p4]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p4,
  baselineEdge p4 p0
]
def witnesses : List BaselineCombination := [
  [(9, (35870006997696790127811118144773985747/61408536520165925600000000000000000000))],
  [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))],
  [(12, (82610740515770295147334845440431333/110907896405987100000000000000000000))],
  [(0, (2525116439092747991754459106829/4457675000000000000000000000000))],
  [(2, (100725405552390045307244760797429/214568800000000000000000000000000))]
]
def margin : ℚ := (7/10)
theorem wall_checked : BaselineWallCheck (15/32) (1/2) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 0 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3, p4]
end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row015
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row015.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row015.domain_checked
