import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row011
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 503b5639d78fd3e2e81417c28b75fc1a3c9374c2ef1c858d0496444e2b5a0378,
    physical cell 0, archived interval [11/32, 3/8]. -/
def p0 : QPoint := ((57489469471497320375359050222611241/49136255200000000000000000000000000), (1607/2290))
def p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def p3 : QPoint := ((1607/2290), (1292829637052239290111771135463841/1020807575000000000000000000000000))
def p4 : QPoint := ((1607/2290), (1607/2290))
def vertices : List QPoint := [p0, p1, p2, p3, p4]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p4,
  baselineEdge p4 p0
]
def witnesses : List BaselineCombination := [
  [(9, (8168440388450644939268746055153242736063/14062554863117996962400000000000000000000))],
  [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))],
  [(12, (18834925540071397588739679605858775257/25397908276971045900000000000000000000))],
  [(0, (576481264552239290111771135463841/1020807575000000000000000000000000))],
  [(2, (100472765552390045307244760797429/214568800000000000000000000000000))]
]
def margin : ℚ := (1607/2290)
theorem wall_checked : BaselineWallCheck (11/32) (3/8) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 0 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3, p4]
end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row011
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row011.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row011.domain_checked
