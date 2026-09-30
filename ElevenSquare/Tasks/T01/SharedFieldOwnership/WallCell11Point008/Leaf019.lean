import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf019p0 : QPoint := ((337708359002281417731/100000000000000000000), (77676721065501633299823210205227/42255200000000000000000000000000))
def leaf019p1 : QPoint := ((337708359002281417731/100000000000000000000), (11643624653062200196085895143171/4457675000000000000000000000000))
def leaf019p2 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf019p3 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf019p4 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))

def leaf019 : WallOwnershipLeaf where
  margin := (1/2)
  polygon := [baselineEdge leaf019p0 leaf019p1, baselineEdge leaf019p1 leaf019p2, baselineEdge leaf019p2 leaf019p3, baselineEdge leaf019p3 leaf019p4, baselineEdge leaf019p4 leaf019p0]
  vertices := [leaf019p0, leaf019p1, leaf019p2, leaf019p3, leaf019p4]
  implications := [[(1, (5829844434576555540234371516085358879/7534397946400000000000000000000000000))], [(23, (124077759535770295147334845440431333/110907896405987100000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (4325560767752863172706125402542912469/3830785591706517600000000000000000000))]]

theorem leaf019_checked : leaf019.Check 11 [point] (7/8) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf019, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf019, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf019p0, leaf019p1, leaf019p2, leaf019p3, leaf019p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf019]
      · intro v hv
        simp only [leaf019, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf019p4, by simp [leaf019], leaf019p1, by simp [leaf019],
            by simp [leaf019], by simp [leaf019], ?_⟩
          norm_num [leaf019p4, leaf019p0, leaf019p1]
        · refine ⟨leaf019p0, by simp [leaf019], leaf019p2, by simp [leaf019],
            by simp [leaf019], by simp [leaf019], ?_⟩
          norm_num [leaf019p0, leaf019p1, leaf019p2]
        · refine ⟨leaf019p1, by simp [leaf019], leaf019p3, by simp [leaf019],
            by simp [leaf019], by simp [leaf019], ?_⟩
          norm_num [leaf019p1, leaf019p2, leaf019p3]
        · refine ⟨leaf019p2, by simp [leaf019], leaf019p4, by simp [leaf019],
            by simp [leaf019], by simp [leaf019], ?_⟩
          norm_num [leaf019p2, leaf019p3, leaf019p4]
        · refine ⟨leaf019p3, by simp [leaf019], leaf019p0, by simp [leaf019],
            by simp [leaf019], by simp [leaf019], ?_⟩
          norm_num [leaf019p3, leaf019p4, leaf019p0]
    · intro v hv
      simp only [leaf019, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf019, point, leaf019p0, leaf019p1, leaf019p2, leaf019p3, leaf019p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
