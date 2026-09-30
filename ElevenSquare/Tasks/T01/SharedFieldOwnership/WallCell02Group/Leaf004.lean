import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf004p0 : QPoint := ((15838390482248717237923594527996921/6081002920000000000000000000000000), (67063/131090))
def leaf004p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf004p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf004p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf004p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf004p5 : QPoint := ((5569002282375107438501788699427626939/2731071380400000000000000000000000000), (67063/131090))

def leaf004 : WallOwnershipLeaf where
  margin := (67063/131090)
  polygon := [baselineEdge leaf004p0 leaf004p1, baselineEdge leaf004p1 leaf004p2, baselineEdge leaf004p2 leaf004p3, baselineEdge leaf004p3 leaf004p4, baselineEdge leaf004p4 leaf004p5, baselineEdge leaf004p5 leaf004p0]
  vertices := [leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4, leaf004p5]
  implications := [[(11, (18819069083266223372423064549322817152331/13350895299146756198400000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (92689352191453777376791002766688745013469/95361951622661561484900000000000000000000))], [(2, (17908795135135275410523626956411693755607/31672234798498800000000000000000000000000))]]

theorem leaf004_polygon_checked : BaselinePolygonCheck leaf004.vertices leaf004.polygon := by
  constructor
  · simp [leaf004]
  · intro v hv
    simp only [leaf004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf004p5, by simp [leaf004], leaf004p1, by simp [leaf004],
        by simp [leaf004], by simp [leaf004], ?_⟩
      norm_num [leaf004p5, leaf004p0, leaf004p1]
    · refine ⟨leaf004p0, by simp [leaf004], leaf004p2, by simp [leaf004],
        by simp [leaf004], by simp [leaf004], ?_⟩
      norm_num [leaf004p0, leaf004p1, leaf004p2]
    · refine ⟨leaf004p1, by simp [leaf004], leaf004p3, by simp [leaf004],
        by simp [leaf004], by simp [leaf004], ?_⟩
      norm_num [leaf004p1, leaf004p2, leaf004p3]
    · refine ⟨leaf004p2, by simp [leaf004], leaf004p4, by simp [leaf004],
        by simp [leaf004], by simp [leaf004], ?_⟩
      norm_num [leaf004p2, leaf004p3, leaf004p4]
    · refine ⟨leaf004p3, by simp [leaf004], leaf004p5, by simp [leaf004],
        by simp [leaf004], by simp [leaf004], ?_⟩
      norm_num [leaf004p3, leaf004p4, leaf004p5]
    · refine ⟨leaf004p4, by simp [leaf004], leaf004p0, by simp [leaf004],
        by simp [leaf004], by simp [leaf004], ?_⟩
      norm_num [leaf004p4, leaf004p5, leaf004p0]

theorem leaf004_checked : leaf004.Check 2 owned (3/256) (1/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf004, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf004, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4, leaf004p5]
  · intro p hp
    constructor
    · exact leaf004_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf004, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4, leaf004p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
