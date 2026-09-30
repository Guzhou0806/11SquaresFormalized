import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf002p0 : QPoint := ((340152734849356704516123/103300000000000000000000), (12025108541613252802556729682895643/4604778275000000000000000000000000))
def leaf002p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf002p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf002p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf002p4 : QPoint := ((340152734849356704516123/103300000000000000000000), (80324011340663187198717376141999491/43649621600000000000000000000000000))

def leaf002 : WallOwnershipLeaf where
  margin := (1207/2066)
  polygon := [baselineEdge leaf002p0 leaf002p1, baselineEdge leaf002p1 leaf002p2, baselineEdge leaf002p2 leaf002p3, baselineEdge leaf002p3 leaf002p4, baselineEdge leaf002p4 leaf002p0]
  vertices := [leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4]
  implications := [[(23, (110134172326750714887196895339965566989/114567856987384674300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (3837322341438227657405427540826828580477/3957201516232832680800000000000000000000))], [(1, (6002601167783421873062105776116175722007/7783033078631200000000000000000000000000))]]

theorem leaf002_checked : leaf002.Check 11 [point] (3/32) (7/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf002, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf002, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf002]
      · intro v hv
        simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf002p4, by simp [leaf002], leaf002p1, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p4, leaf002p0, leaf002p1]
        · refine ⟨leaf002p0, by simp [leaf002], leaf002p2, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p0, leaf002p1, leaf002p2]
        · refine ⟨leaf002p1, by simp [leaf002], leaf002p3, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p1, leaf002p2, leaf002p3]
        · refine ⟨leaf002p2, by simp [leaf002], leaf002p4, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p2, leaf002p3, leaf002p4]
        · refine ⟨leaf002p3, by simp [leaf002], leaf002p0, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p3, leaf002p4, leaf002p0]
    · intro v hv
      simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf002, point, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007
