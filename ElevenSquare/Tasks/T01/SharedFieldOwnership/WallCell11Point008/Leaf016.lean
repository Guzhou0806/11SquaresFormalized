import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf016p0 : QPoint := ((28556043951203046178059/8900000000000000000000), (1035807469122535817451644667742219/396733075000000000000000000000000))
def leaf016p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf016p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf016p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf016p4 : QPoint := ((28556043951203046178059/8900000000000000000000), (6927703774829645363684265708265203/3760712800000000000000000000000000))

def leaf016 : WallOwnershipLeaf where
  margin := (119/178)
  polygon := [baselineEdge leaf016p0 leaf016p1, baselineEdge leaf016p1 leaf016p2, baselineEdge leaf016p2 leaf016p3, baselineEdge leaf016p3 leaf016p4, baselineEdge leaf016p4 leaf016p0]
  vertices := [leaf016p0, leaf016p1, leaf016p2, leaf016p3, leaf016p4]
  implications := [[(23, (7932894172183556268112801244198388637/9870802780132851900000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (276184920114404822370845160826319209741/340939917661880066400000000000000000000))], [(1, (515471993792113443080859064931596940231/670561417229600000000000000000000000000))]]

theorem leaf016_checked : leaf016.Check 11 [point] (1/2) (5/8) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf016, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf016, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf016p0, leaf016p1, leaf016p2, leaf016p3, leaf016p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf016]
      · intro v hv
        simp only [leaf016, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf016p4, by simp [leaf016], leaf016p1, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p4, leaf016p0, leaf016p1]
        · refine ⟨leaf016p0, by simp [leaf016], leaf016p2, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p0, leaf016p1, leaf016p2]
        · refine ⟨leaf016p1, by simp [leaf016], leaf016p3, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p1, leaf016p2, leaf016p3]
        · refine ⟨leaf016p2, by simp [leaf016], leaf016p4, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p2, leaf016p3, leaf016p4]
        · refine ⟨leaf016p3, by simp [leaf016], leaf016p0, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p3, leaf016p4, leaf016p0]
    · intro v hv
      simp only [leaf016, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf016, point, leaf016p0, leaf016p1, leaf016p2, leaf016p3, leaf016p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
