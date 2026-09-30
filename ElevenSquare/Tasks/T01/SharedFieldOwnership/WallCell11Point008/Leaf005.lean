import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf005p0 : QPoint := ((340756068593393207199819/104900000000000000000000), (12209886136062248005694104005186379/4676101075000000000000000000000000))
def leaf005p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf005p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf005p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf005p4 : QPoint := ((340756068593393207199819/104900000000000000000000), (81613160797711213331514547505283123/44325704800000000000000000000000000))

def leaf005 : WallOwnershipLeaf where
  margin := (1319/2098)
  polygon := [baselineEdge leaf005p0 leaf005p1, baselineEdge leaf005p1 leaf005p2, baselineEdge leaf005p2 leaf005p3, baselineEdge leaf005p3 leaf005p4, baselineEdge leaf005p4 leaf005p0]
  vertices := [leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4]
  implications := [[(23, (102167331914523039609554252867012468317/116342383329880467900000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (3558403351432353468168725547267515179981/4018494085700136962400000000000000000000))], [(1, (6085049363904006761705855720373541464071/7903583445773600000000000000000000000000))]]

theorem leaf005_checked : leaf005.Check 11 [point] (5/32) (21/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf005, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf005, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf005]
      · intro v hv
        simp only [leaf005, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf005p4, by simp [leaf005], leaf005p1, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p4, leaf005p0, leaf005p1]
        · refine ⟨leaf005p0, by simp [leaf005], leaf005p2, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p0, leaf005p1, leaf005p2]
        · refine ⟨leaf005p1, by simp [leaf005], leaf005p3, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p1, leaf005p2, leaf005p3]
        · refine ⟨leaf005p2, by simp [leaf005], leaf005p4, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p2, leaf005p3, leaf005p4]
        · refine ⟨leaf005p3, by simp [leaf005], leaf005p0, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p3, leaf005p4, leaf005p0]
    · intro v hv
      simp only [leaf005, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf005, point, leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
