import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 503b5639d78fd3e2e81417c28b75fc1a3c9374c2ef1c858d0496444e2b5a0378,
    physical cell 0, archived interval [3/32, 1/8]. -/
def p0 : QPoint := ((250840128175618916802383837903744157/221649570400000000000000000000000000), (1207/2066))
def p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def p3 : QPoint := ((1207/2066), (5828001744082808675482356257354357/4604778275000000000000000000000000))
def p4 : QPoint := ((1207/2066), (1207/2066))
def vertices : List QPoint := [p0, p1, p2, p3, p4]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p4,
  baselineEdge p4 p0
]
def witnesses : List BaselineCombination := [
  [(9, (50745290221174864202028885043551527276651/63435018225331401144800000000000000000000))],
  [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))],
  [(12, (110134172326750714887196895339965566989/114567856987384674300000000000000000000))],
  [(0, (3137794881582808675482356257354357/4604778275000000000000000000000000))],
  [(2, (121347857375618916802383837903744157/221649570400000000000000000000000000))]
]
def margin : ℚ := (1207/2066)
theorem wall_checked : BaselineWallCheck (3/32) (1/8) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 0 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3, p4]
end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row003
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row003.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row003.domain_checked
