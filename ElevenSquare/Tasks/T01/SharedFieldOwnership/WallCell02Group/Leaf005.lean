import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf005p0 : QPoint := ((4951144258151086621692956501731893/1900516360000000000000000000000000), (4223/8194))
def leaf005p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf005p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf005p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf005p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf005p5 : QPoint := ((1739338451322683284426106362159965487/853550953200000000000000000000000000), (4223/8194))

def leaf005 : WallOwnershipLeaf where
  margin := (4223/8194)
  polygon := [baselineEdge leaf005p0 leaf005p1, baselineEdge leaf005p1 leaf005p2, baselineEdge leaf005p2 leaf005p3, baselineEdge leaf005p3 leaf005p4, baselineEdge leaf005p4 leaf005p5, baselineEdge leaf005p5 leaf005p0]
  vertices := [leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4, leaf005p5]
  implications := [[(11, (5847430673920614654727080285191515895423/4172600354001392947200000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (28751225829301878720933155720125393875977/29803792493557435151700000000000000000000))], [(2, (5616382222722380000069822232086254429531/9898630404260400000000000000000000000000))]]

theorem leaf005_polygon_checked : BaselinePolygonCheck leaf005.vertices leaf005.polygon := by
  constructor
  · simp [leaf005]
  · intro v hv
    simp only [leaf005, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf005p5, by simp [leaf005], leaf005p1, by simp [leaf005],
        by simp [leaf005], by simp [leaf005], ?_⟩
      norm_num [leaf005p5, leaf005p0, leaf005p1]
    · refine ⟨leaf005p0, by simp [leaf005], leaf005p2, by simp [leaf005],
        by simp [leaf005], by simp [leaf005], ?_⟩
      norm_num [leaf005p0, leaf005p1, leaf005p2]
    · refine ⟨leaf005p1, by simp [leaf005], leaf005p3, by simp [leaf005],
        by simp [leaf005], by simp [leaf005], ?_⟩
      norm_num [leaf005p1, leaf005p2, leaf005p3]
    · refine ⟨leaf005p2, by simp [leaf005], leaf005p4, by simp [leaf005],
        by simp [leaf005], by simp [leaf005], ?_⟩
      norm_num [leaf005p2, leaf005p3, leaf005p4]
    · refine ⟨leaf005p3, by simp [leaf005], leaf005p5, by simp [leaf005],
        by simp [leaf005], by simp [leaf005], ?_⟩
      norm_num [leaf005p3, leaf005p4, leaf005p5]
    · refine ⟨leaf005p4, by simp [leaf005], leaf005p0, by simp [leaf005],
        by simp [leaf005], by simp [leaf005], ?_⟩
      norm_num [leaf005p4, leaf005p5, leaf005p0]

theorem leaf005_checked : leaf005.Check 2 owned (1/64) (3/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf005, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf005, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4, leaf005p5]
  · intro p hp
    constructor
    · exact leaf005_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf005, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf005, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4, leaf005p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
