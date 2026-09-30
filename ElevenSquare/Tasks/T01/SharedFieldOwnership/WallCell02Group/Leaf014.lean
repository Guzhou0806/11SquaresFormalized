import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf014p0 : QPoint := ((1276243141330849369332660817748781/486610120000000000000000000000000), (1319/2098))
def leaf014p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf014p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf014p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf014p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf014p5 : QPoint := ((436474022411104409412493427851062679/218544044400000000000000000000000000), (1319/2098))

def leaf014 : WallOwnershipLeaf where
  margin := (1319/2098)
  polygon := [baselineEdge leaf014p0 leaf014p1, baselineEdge leaf014p1 leaf014p2, baselineEdge leaf014p2 leaf014p3, baselineEdge leaf014p3 leaf014p4, baselineEdge leaf014p4 leaf014p5, baselineEdge leaf014p5 leaf014p0]
  vertices := [leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4, leaf014p5]
  implications := [[(11, (1236203182144556654334563636603832114791/1068356790663280742400000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (5701247693446358696182299328877602679009/7630993001157371118900000000000000000000))], [(2, (1585382776974604710781850993765799584227/2534455282906800000000000000000000000000))]]

theorem leaf014_polygon_checked : BaselinePolygonCheck leaf014.vertices leaf014.polygon := by
  constructor
  · simp [leaf014]
  · intro v hv
    simp only [leaf014, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf014p5, by simp [leaf014], leaf014p1, by simp [leaf014],
        by simp [leaf014], by simp [leaf014], ?_⟩
      norm_num [leaf014p5, leaf014p0, leaf014p1]
    · refine ⟨leaf014p0, by simp [leaf014], leaf014p2, by simp [leaf014],
        by simp [leaf014], by simp [leaf014], ?_⟩
      norm_num [leaf014p0, leaf014p1, leaf014p2]
    · refine ⟨leaf014p1, by simp [leaf014], leaf014p3, by simp [leaf014],
        by simp [leaf014], by simp [leaf014], ?_⟩
      norm_num [leaf014p1, leaf014p2, leaf014p3]
    · refine ⟨leaf014p2, by simp [leaf014], leaf014p4, by simp [leaf014],
        by simp [leaf014], by simp [leaf014], ?_⟩
      norm_num [leaf014p2, leaf014p3, leaf014p4]
    · refine ⟨leaf014p3, by simp [leaf014], leaf014p5, by simp [leaf014],
        by simp [leaf014], by simp [leaf014], ?_⟩
      norm_num [leaf014p3, leaf014p4, leaf014p5]
    · refine ⟨leaf014p4, by simp [leaf014], leaf014p0, by simp [leaf014],
        by simp [leaf014], by simp [leaf014], ?_⟩
      norm_num [leaf014p4, leaf014p5, leaf014p0]

theorem leaf014_checked : leaf014.Check 2 owned (5/32) (3/16) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf014, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf014, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4, leaf014p5]
  · intro p hp
    constructor
    · exact leaf014_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf014, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf014, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4, leaf014p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
