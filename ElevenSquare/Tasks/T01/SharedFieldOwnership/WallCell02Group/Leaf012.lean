import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf012p0 : QPoint := ((1253473753505021352259903360090077/479188040000000000000000000000000), (1207/2066))
def leaf012p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf012p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf012p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf012p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf012p5 : QPoint := ((433243950439915018992474462316632743/215210674800000000000000000000000000), (1207/2066))

def leaf012 : WallOwnershipLeaf where
  margin := (1207/2066)
  polygon := [baselineEdge leaf012p0 leaf012p1, baselineEdge leaf012p1 leaf012p2, baselineEdge leaf012p2 leaf012p3, baselineEdge leaf012p3 leaf012p4, baselineEdge leaf012p4 leaf012p5, baselineEdge leaf012p5 leaf012p0]
  vertices := [leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4, leaf012p5]
  implications := [[(11, (1318211483563350680579222341860589680247/1052061548860980940800000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (6255943645952935493952636040734569654353/7514600352903302541300000000000000000000))], [(2, (1504250069766323685641231722173566225459/2495798195655600000000000000000000000000))]]

theorem leaf012_polygon_checked : BaselinePolygonCheck leaf012.vertices leaf012.polygon := by
  constructor
  · simp [leaf012]
  · intro v hv
    simp only [leaf012, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf012p5, by simp [leaf012], leaf012p1, by simp [leaf012],
        by simp [leaf012], by simp [leaf012], ?_⟩
      norm_num [leaf012p5, leaf012p0, leaf012p1]
    · refine ⟨leaf012p0, by simp [leaf012], leaf012p2, by simp [leaf012],
        by simp [leaf012], by simp [leaf012], ?_⟩
      norm_num [leaf012p0, leaf012p1, leaf012p2]
    · refine ⟨leaf012p1, by simp [leaf012], leaf012p3, by simp [leaf012],
        by simp [leaf012], by simp [leaf012], ?_⟩
      norm_num [leaf012p1, leaf012p2, leaf012p3]
    · refine ⟨leaf012p2, by simp [leaf012], leaf012p4, by simp [leaf012],
        by simp [leaf012], by simp [leaf012], ?_⟩
      norm_num [leaf012p2, leaf012p3, leaf012p4]
    · refine ⟨leaf012p3, by simp [leaf012], leaf012p5, by simp [leaf012],
        by simp [leaf012], by simp [leaf012], ?_⟩
      norm_num [leaf012p3, leaf012p4, leaf012p5]
    · refine ⟨leaf012p4, by simp [leaf012], leaf012p0, by simp [leaf012],
        by simp [leaf012], by simp [leaf012], ?_⟩
      norm_num [leaf012p4, leaf012p5, leaf012p0]

theorem leaf012_checked : leaf012.Check 2 owned (3/32) (1/8) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf012, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf012, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4, leaf012p5]
  · intro p hp
    constructor
    · exact leaf012_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf012, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf012, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4, leaf012p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
