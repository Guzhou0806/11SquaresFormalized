import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf003p0 : QPoint := ((3958393381677400746714136796723313/1520134760000000000000000000000000), (16639/32770))
def leaf003p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf003p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf003p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf003p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf003p5 : QPoint := ((1393080409039227025400134378520431267/682715761200000000000000000000000000), (16639/32770))

def leaf003 : WallOwnershipLeaf where
  margin := (16639/32770)
  polygon := [baselineEdge leaf003p0 leaf003p1, baselineEdge leaf003p1 leaf003p2, baselineEdge leaf003p2 leaf003p3, baselineEdge leaf003p3 leaf003p4, baselineEdge leaf003p4 leaf003p5, baselineEdge leaf003p5 leaf003p0]
  vertices := [leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4, leaf003p5]
  implications := [[(11, (4731955654124560499765838929600341125043/3337469211633528115200000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (23345815368914179606662912202794951362357/23838669270536420549700000000000000000000))], [(2, (4461303001566841461613084562984294792671/7917454682636400000000000000000000000000))]]

theorem leaf003_polygon_checked : BaselinePolygonCheck leaf003.vertices leaf003.polygon := by
  constructor
  · simp [leaf003]
  · intro v hv
    simp only [leaf003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf003p5, by simp [leaf003], leaf003p1, by simp [leaf003],
        by simp [leaf003], by simp [leaf003], ?_⟩
      norm_num [leaf003p5, leaf003p0, leaf003p1]
    · refine ⟨leaf003p0, by simp [leaf003], leaf003p2, by simp [leaf003],
        by simp [leaf003], by simp [leaf003], ?_⟩
      norm_num [leaf003p0, leaf003p1, leaf003p2]
    · refine ⟨leaf003p1, by simp [leaf003], leaf003p3, by simp [leaf003],
        by simp [leaf003], by simp [leaf003], ?_⟩
      norm_num [leaf003p1, leaf003p2, leaf003p3]
    · refine ⟨leaf003p2, by simp [leaf003], leaf003p4, by simp [leaf003],
        by simp [leaf003], by simp [leaf003], ?_⟩
      norm_num [leaf003p2, leaf003p3, leaf003p4]
    · refine ⟨leaf003p3, by simp [leaf003], leaf003p5, by simp [leaf003],
        by simp [leaf003], by simp [leaf003], ?_⟩
      norm_num [leaf003p3, leaf003p4, leaf003p5]
    · refine ⟨leaf003p4, by simp [leaf003], leaf003p0, by simp [leaf003],
        by simp [leaf003], by simp [leaf003], ?_⟩
      norm_num [leaf003p4, leaf003p5, leaf003p0]

theorem leaf003_checked : leaf003.Check 2 owned (1/128) (3/256) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf003, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf003, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4, leaf003p5]
  · intro p hp
    constructor
    · exact leaf003_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf003, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4, leaf003p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
