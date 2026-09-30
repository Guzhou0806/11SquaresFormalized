import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 503b5639d78fd3e2e81417c28b75fc1a3c9374c2ef1c858d0496444e2b5a0378,
    physical cell 0, archived interval [5/32, 3/16]. -/
def p0 : QPoint := ((257987876744457157527299754076503021/225082671200000000000000000000000000), (1319/2098))
def p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def p3 : QPoint := ((1319/2098), (5919748607108292643350427603063621/4676101075000000000000000000000000))
def p4 : QPoint := ((1319/2098), (1319/2098))
def vertices : List QPoint := [p0, p1, p2, p3, p4]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p4,
  baselineEdge p4 p0
]
def witnesses : List BaselineCombination := [
  [(9, (46190594362682972844073862933867911048603/64417554809654055954400000000000000000000))],
  [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))],
  [(12, (102167331914523039609554252867012468317/116342383329880467900000000000000000000))],
  [(0, (2979911944608292643350427603063621/4676101075000000000000000000000000))],
  [(2, (116479753144457157527299754076503021/225082671200000000000000000000000000))]
]
def margin : ℚ := (1319/2098)
theorem wall_checked : BaselineWallCheck (5/32) (3/16) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 0 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3, p4]
end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row005
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row005.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.WallChunks.Cell00Row005.domain_checked
