import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf007p0 : QPoint := ((1365816149912620738571627/421700000000000000000000), (49082698636963298226894219818752107/18798015475000000000000000000000000))
def leaf007p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf007p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf007p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf007p4 : QPoint := ((1365816149912620738571627/421700000000000000000000), (328125351053220387625354477435442259/178190178400000000000000000000000000))

def leaf007 : WallOwnershipLeaf where
  margin := (5383/8434)
  polygon := [baselineEdge leaf007p0 leaf007p1, baselineEdge leaf007p1 leaf007p2, baselineEdge leaf007p2 leaf007p3, baselineEdge leaf007p3 leaf007p4, baselineEdge leaf007p4 leaf007p0]
  vertices := [leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4]
  implications := [[(23, (402359551519043334636311043222298931261/467698599144047600700000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (14012585548967503999301730822523461881773/16154422840226384719200000000000000000000))], [(1, (24452922927537894713168344683331958392743/31772556139968800000000000000000000000000))]]

theorem leaf007_checked : leaf007.Check 11 [point] (11/64) (23/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf007, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf007, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf007]
      · intro v hv
        simp only [leaf007, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf007p4, by simp [leaf007], leaf007p1, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p4, leaf007p0, leaf007p1]
        · refine ⟨leaf007p0, by simp [leaf007], leaf007p2, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p0, leaf007p1, leaf007p2]
        · refine ⟨leaf007p1, by simp [leaf007], leaf007p3, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p1, leaf007p2, leaf007p3]
        · refine ⟨leaf007p2, by simp [leaf007], leaf007p4, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p2, leaf007p3, leaf007p4]
        · refine ⟨leaf007p3, by simp [leaf007], leaf007p0, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p3, leaf007p4, leaf007p0]
    · intro v hv
      simp only [leaf007, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf007, point, leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
