import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf010p0 : QPoint := ((311373867952362524231166663642933/119217160000000000000000000000000), (287/514))
def leaf010p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf010p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf010p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf010p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf010p5 : QPoint := ((108282445437229583621554633896780847/53542249200000000000000000000000000), (287/514))

def leaf010 : WallOwnershipLeaf where
  margin := (287/514)
  polygon := [baselineEdge leaf010p0 leaf010p1, baselineEdge leaf010p1 leaf010p2, baselineEdge leaf010p2 leaf010p3, baselineEdge leaf010p3 leaf010p4, baselineEdge leaf010p4 leaf010p5, baselineEdge leaf010p5 leaf010p0]
  vertices := [leaf010p0, leaf010p1, leaf010p2, leaf010p3, leaf010p4, leaf010p5]
  implications := [[(11, (342546295777740953445169546813331604863/261742321449440563200000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (1649222430267510185813966565797467958537/1869556912580976527700000000000000000000))], [(2, (366005020368853966321197049950248325211/620929463972400000000000000000000000000))]]

theorem leaf010_polygon_checked : BaselinePolygonCheck leaf010.vertices leaf010.polygon := by
  constructor
  · simp [leaf010]
  · intro v hv
    simp only [leaf010, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf010p5, by simp [leaf010], leaf010p1, by simp [leaf010],
        by simp [leaf010], by simp [leaf010], ?_⟩
      norm_num [leaf010p5, leaf010p0, leaf010p1]
    · refine ⟨leaf010p0, by simp [leaf010], leaf010p2, by simp [leaf010],
        by simp [leaf010], by simp [leaf010], ?_⟩
      norm_num [leaf010p0, leaf010p1, leaf010p2]
    · refine ⟨leaf010p1, by simp [leaf010], leaf010p3, by simp [leaf010],
        by simp [leaf010], by simp [leaf010], ?_⟩
      norm_num [leaf010p1, leaf010p2, leaf010p3]
    · refine ⟨leaf010p2, by simp [leaf010], leaf010p4, by simp [leaf010],
        by simp [leaf010], by simp [leaf010], ?_⟩
      norm_num [leaf010p2, leaf010p3, leaf010p4]
    · refine ⟨leaf010p3, by simp [leaf010], leaf010p5, by simp [leaf010],
        by simp [leaf010], by simp [leaf010], ?_⟩
      norm_num [leaf010p3, leaf010p4, leaf010p5]
    · refine ⟨leaf010p4, by simp [leaf010], leaf010p0, by simp [leaf010],
        by simp [leaf010], by simp [leaf010], ?_⟩
      norm_num [leaf010p4, leaf010p5, leaf010p0]

theorem leaf010_checked : leaf010.Check 2 owned (1/16) (5/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf010, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf010, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf010p0, leaf010p1, leaf010p2, leaf010p3, leaf010p4, leaf010p5]
  · intro p hp
    constructor
    · exact leaf010_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf010, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf010, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf010p0, leaf010p1, leaf010p2, leaf010p3, leaf010p4, leaf010p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
