import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf006p0 : QPoint := ((19819458098299917742107062712445917/7604384840000000000000000000000000), (17143/32786))
def leaf006p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf006p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf006p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf006p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf006p5 : QPoint := ((6950306143581729822210681375369371303/3415245490800000000000000000000000000), (17143/32786))

def leaf006 : WallOwnershipLeaf where
  margin := (17143/32786)
  polygon := [baselineEdge leaf006p0 leaf006p1, baselineEdge leaf006p1 leaf006p2, baselineEdge leaf006p2 leaf006p3, baselineEdge leaf006p3 leaf006p4, baselineEdge leaf006p4 leaf006p5, baselineEdge leaf006p5 leaf006p0]
  vertices := [leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4, leaf006p5]
  implications := [[(11, (23126980153300925485706865295373326842487/16695493679068790476800000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (113323128522420009634429392658046273324113/119251542676809137037300000000000000000000))], [(2, (22624767017486987820635732450717590642739/39606601956807600000000000000000000000000))]]

theorem leaf006_polygon_checked : BaselinePolygonCheck leaf006.vertices leaf006.polygon := by
  constructor
  · simp [leaf006]
  · intro v hv
    simp only [leaf006, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf006p5, by simp [leaf006], leaf006p1, by simp [leaf006],
        by simp [leaf006], by simp [leaf006], ?_⟩
      norm_num [leaf006p5, leaf006p0, leaf006p1]
    · refine ⟨leaf006p0, by simp [leaf006], leaf006p2, by simp [leaf006],
        by simp [leaf006], by simp [leaf006], ?_⟩
      norm_num [leaf006p0, leaf006p1, leaf006p2]
    · refine ⟨leaf006p1, by simp [leaf006], leaf006p3, by simp [leaf006],
        by simp [leaf006], by simp [leaf006], ?_⟩
      norm_num [leaf006p1, leaf006p2, leaf006p3]
    · refine ⟨leaf006p2, by simp [leaf006], leaf006p4, by simp [leaf006],
        by simp [leaf006], by simp [leaf006], ?_⟩
      norm_num [leaf006p2, leaf006p3, leaf006p4]
    · refine ⟨leaf006p3, by simp [leaf006], leaf006p5, by simp [leaf006],
        by simp [leaf006], by simp [leaf006], ?_⟩
      norm_num [leaf006p3, leaf006p4, leaf006p5]
    · refine ⟨leaf006p4, by simp [leaf006], leaf006p0, by simp [leaf006],
        by simp [leaf006], by simp [leaf006], ?_⟩
      norm_num [leaf006p4, leaf006p5, leaf006p0]

theorem leaf006_checked : leaf006.Check 2 owned (3/128) (1/32) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf006, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf006, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4, leaf006p5]
  · intro p hp
    constructor
    · exact leaf006_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf006, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf006, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4, leaf006p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
