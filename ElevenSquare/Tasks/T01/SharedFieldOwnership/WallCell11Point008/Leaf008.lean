import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf008p0 : QPoint := ((5470161475805585618084403/1691300000000000000000000), (196852128632240991916400744556451123/75392657275000000000000000000000000))
def leaf008p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf008p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf008p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf008p4 : QPoint := ((5470161475805585618084403/1691300000000000000000000), (1316076954980829123999909954201004251/714662197600000000000000000000000000))

def leaf008 : WallOwnershipLeaf where
  margin := (21743/33826)
  polygon := [baselineEdge leaf008p0 leaf008p1, baselineEdge leaf008p1 leaf008p2, baselineEdge leaf008p2 leaf008p3, baselineEdge leaf008p3 leaf008p4, baselineEdge leaf008p4 leaf008p0]
  vertices := [leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4]
  implications := [[(23, (1597812892361983001826874240934015135029/1875785251914459822300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (55643021162292574839978698933208278588197/64790076712532332168800000000000000000000))], [(1, (98055309019476083851983925451551674720527/127429272467463200000000000000000000000000))]]

theorem leaf008_checked : leaf008.Check 11 [point] (23/128) (3/16) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf008, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf008, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf008]
      · intro v hv
        simp only [leaf008, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf008p4, by simp [leaf008], leaf008p1, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p4, leaf008p0, leaf008p1]
        · refine ⟨leaf008p0, by simp [leaf008], leaf008p2, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p0, leaf008p1, leaf008p2]
        · refine ⟨leaf008p1, by simp [leaf008], leaf008p3, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p1, leaf008p2, leaf008p3]
        · refine ⟨leaf008p2, by simp [leaf008], leaf008p4, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p2, leaf008p3, leaf008p4]
        · refine ⟨leaf008p3, by simp [leaf008], leaf008p0, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p3, leaf008p4, leaf008p0]
    · intro v hv
      simp only [leaf008, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf008, point, leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
