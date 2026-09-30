import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf006p0 : QPoint := ((218289725608535394132963/67300000000000000000000), (7833312442510860731965807431354083/3000015275000000000000000000000000))
def leaf006p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf006p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf006p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf006p4 : QPoint := ((218289725608535394132963/67300000000000000000000), (52363171072282599210781020468117771/28437749600000000000000000000000000))

def leaf006 : WallOwnershipLeaf where
  margin := (21319/33650)
  polygon := [baselineEdge leaf006p0 leaf006p1, baselineEdge leaf006p1 leaf006p2, baselineEdge leaf006p2 leaf006p3, baselineEdge leaf006p3 leaf006p4, baselineEdge leaf006p4 leaf006p0]
  vertices := [leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4]
  implications := [[(23, (64869053819985408634156350981410287109/74641014281229318300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (2259232787309801715231222395911380091637/2578118703218486344800000000000000000000))], [(1, (3903207412445903478577732030325446525567/5070649817927200000000000000000000000000))]]

theorem leaf006_checked : leaf006.Check 11 [point] (21/128) (11/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf006, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf006, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf006]
      · intro v hv
        simp only [leaf006, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf006p4, by simp [leaf006], leaf006p1, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p4, leaf006p0, leaf006p1]
        · refine ⟨leaf006p0, by simp [leaf006], leaf006p2, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p0, leaf006p1, leaf006p2]
        · refine ⟨leaf006p1, by simp [leaf006], leaf006p3, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p1, leaf006p2, leaf006p3]
        · refine ⟨leaf006p2, by simp [leaf006], leaf006p4, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p2, leaf006p3, leaf006p4]
        · refine ⟨leaf006p3, by simp [leaf006], leaf006p0, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p3, leaf006p4, leaf006p0]
    · intro v hv
      simp only [leaf006, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf006, point, leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
