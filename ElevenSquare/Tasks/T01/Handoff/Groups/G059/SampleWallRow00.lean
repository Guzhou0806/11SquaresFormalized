import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059.SampleWallRow00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
def p0 : QPoint := ((1/2), (1/2))
def p1 : QPoint := ((236937085552390045307244760797429/214568800000000000000000000000000), (1/2))
def p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p3 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def p4 : QPoint := ((1/2), (5639153939092747991754459106829/4457675000000000000000000000000))
def vertices : List QPoint := [p0, p1, p2, p3, p4]
def polygon : Polygon := [baselineEdge p0 p1, baselineEdge p1 p2,
  baselineEdge p2 p3, baselineEdge p3 p4, baselineEdge p4 p0]
def witnesses : List BaselineCombination := [
  [(2, (129652685552390045307244760797429/214568800000000000000000000000000))],
  [(9, (58765614008656790127811118144773985747/61408536520165925600000000000000000000))],
  [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))],
  [(12, (124077759535770295147334845440431333/110907896405987100000000000000000000))],
  [(0, (3410316439092747991754459106829/4457675000000000000000000000000))]
]
theorem wall_checked : BaselineWallCheck 0 (1/32) (1/2) := by
  norm_num [BaselineWallCheck]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 0 (1/2)) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3, p4]
end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059.SampleWallRow00
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.SampleWallRow00.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.SampleWallRow00.domain_checked
