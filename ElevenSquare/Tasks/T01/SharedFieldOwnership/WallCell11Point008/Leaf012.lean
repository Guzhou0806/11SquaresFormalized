import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf012p0 : QPoint := ((5506503147606041901630603/1711300000000000000000000), (199170970962853431955617923585085323/76284192275000000000000000000000000))
def leaf012p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf012p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf012p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf012p4 : QPoint := ((5506503147606041901630603/1711300000000000000000000), (1331913391673929450659874596242049651/723113237600000000000000000000000000))

def leaf012 : WallOwnershipLeaf where
  margin := (22567/34226)
  polygon := [baselineEdge leaf012p0 leaf012p1, baselineEdge leaf012p1 leaf012p2, baselineEdge leaf012p2 leaf012p3, baselineEdge leaf012p3 leaf012p4, baselineEdge leaf012p4 leaf012p0]
  vertices := [leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4]
  implications := [[(23, (1557939894597937060856341210022101401629/1897966831195657242300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (54245301560958667474519924013716861081997/65556233830873635688800000000000000000000))], [(1, (99150887359979234960030799754768746496327/128936152056743200000000000000000000000000))]]

theorem leaf012_checked : leaf012.Check 11 [point] (27/128) (7/32) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf012, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf012, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf012]
      · intro v hv
        simp only [leaf012, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf012p4, by simp [leaf012], leaf012p1, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p4, leaf012p0, leaf012p1]
        · refine ⟨leaf012p0, by simp [leaf012], leaf012p2, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p0, leaf012p1, leaf012p2]
        · refine ⟨leaf012p1, by simp [leaf012], leaf012p3, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p1, leaf012p2, leaf012p3]
        · refine ⟨leaf012p2, by simp [leaf012], leaf012p4, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p2, leaf012p3, leaf012p4]
        · refine ⟨leaf012p3, by simp [leaf012], leaf012p0, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p3, leaf012p4, leaf012p0]
    · intro v hv
      simp only [leaf012, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf012, point, leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
