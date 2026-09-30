import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf011p0 : QPoint := ((4996802979889828647302092688219949/1911649480000000000000000000000000), (4711/8242))
def leaf011p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf011p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf011p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf011p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf011p5 : QPoint := ((1732247175279467370056134810461610391/858551007600000000000000000000000000), (4711/8242))

def leaf011 : WallOwnershipLeaf where
  margin := (4711/8242)
  polygon := [baselineEdge leaf011p0 leaf011p1, baselineEdge leaf011p1 leaf011p2, baselineEdge leaf011p2 leaf011p3, baselineEdge leaf011p3 leaf011p4, baselineEdge leaf011p4 leaf011p5, baselineEdge leaf011p5 leaf011p0]
  vertices := [leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4, leaf011p5]
  implications := [[(11, (5373136817069223615360092227306379547239/4197043216704842649600000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (25684467367758013524277650652339943412961/29978381465938538018100000000000000000000))], [(2, (5936428180712401537780751139474604467683/9956616035137200000000000000000000000000))]]

theorem leaf011_polygon_checked : BaselinePolygonCheck leaf011.vertices leaf011.polygon := by
  constructor
  · simp [leaf011]
  · intro v hv
    simp only [leaf011, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf011p5, by simp [leaf011], leaf011p1, by simp [leaf011],
        by simp [leaf011], by simp [leaf011], ?_⟩
      norm_num [leaf011p5, leaf011p0, leaf011p1]
    · refine ⟨leaf011p0, by simp [leaf011], leaf011p2, by simp [leaf011],
        by simp [leaf011], by simp [leaf011], ?_⟩
      norm_num [leaf011p0, leaf011p1, leaf011p2]
    · refine ⟨leaf011p1, by simp [leaf011], leaf011p3, by simp [leaf011],
        by simp [leaf011], by simp [leaf011], ?_⟩
      norm_num [leaf011p1, leaf011p2, leaf011p3]
    · refine ⟨leaf011p2, by simp [leaf011], leaf011p4, by simp [leaf011],
        by simp [leaf011], by simp [leaf011], ?_⟩
      norm_num [leaf011p2, leaf011p3, leaf011p4]
    · refine ⟨leaf011p3, by simp [leaf011], leaf011p5, by simp [leaf011],
        by simp [leaf011], by simp [leaf011], ?_⟩
      norm_num [leaf011p3, leaf011p4, leaf011p5]
    · refine ⟨leaf011p4, by simp [leaf011], leaf011p0, by simp [leaf011],
        by simp [leaf011], by simp [leaf011], ?_⟩
      norm_num [leaf011p4, leaf011p5, leaf011p0]

theorem leaf011_checked : leaf011.Check 2 owned (5/64) (3/32) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf011, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf011, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4, leaf011p5]
  · intro p hp
    constructor
    · exact leaf011_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf011, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf011, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4, leaf011p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
