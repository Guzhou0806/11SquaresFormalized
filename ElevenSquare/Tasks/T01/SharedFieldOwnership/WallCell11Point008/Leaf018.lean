import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf018p0 : QPoint := ((37461044567257800203603/11300000000000000000000), (1315507860796028622157706151178323/503717275000000000000000000000000))
def leaf018p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf018p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf018p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf018p4 : QPoint := ((37461044567257800203603/11300000000000000000000), (8784224760401684562880022753190651/4774837600000000000000000000000000))

def leaf018 : WallOwnershipLeaf where
  margin := (127/226)
  polygon := [baselineEdge leaf018p0 leaf018p1, baselineEdge leaf018p1 leaf018p2, baselineEdge leaf018p2 leaf018p3, baselineEdge leaf018p3 leaf018p4, baselineEdge leaf018p4 leaf018p0]
  vertices := [leaf018p0, leaf018p1, leaf018p2, leaf018p3, leaf018p4]
  implications := [[(23, (12569441161842043351648837534768740629/12532592293876542300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (438019705588793538515792170487349108997/432878771862836488800000000000000000000))], [(1, (657193146027390776046483981317645553327/851386967943200000000000000000000000000))]]

theorem leaf018_checked : leaf018.Check 11 [point] (3/4) (7/8) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf018, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf018, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf018p0, leaf018p1, leaf018p2, leaf018p3, leaf018p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf018]
      · intro v hv
        simp only [leaf018, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf018p4, by simp [leaf018], leaf018p1, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p4, leaf018p0, leaf018p1]
        · refine ⟨leaf018p0, by simp [leaf018], leaf018p2, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p0, leaf018p1, leaf018p2]
        · refine ⟨leaf018p1, by simp [leaf018], leaf018p3, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p1, leaf018p2, leaf018p3]
        · refine ⟨leaf018p2, by simp [leaf018], leaf018p4, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p2, leaf018p3, leaf018p4]
        · refine ⟨leaf018p3, by simp [leaf018], leaf018p0, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p3, leaf018p4, leaf018p0]
    · intro v hv
      simp only [leaf018, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf018, point, leaf018p0, leaf018p1, leaf018p2, leaf018p3, leaf018p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
