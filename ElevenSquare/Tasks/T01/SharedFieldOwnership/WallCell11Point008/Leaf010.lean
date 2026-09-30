import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf010p0 : QPoint := ((5486581478269804634186579/1700900000000000000000000), (197964848598934963135224990490195539/75820594075000000000000000000000000))
def leaf010p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf010p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf010p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf010p4 : QPoint := ((5486581478269804634186579/1700900000000000000000000), (1323688326603117280796692982380706043/718718696800000000000000000000000000))

def leaf010 : WallOwnershipLeaf where
  margin := (22159/34018)
  polygon := [baselineEdge leaf010p0 leaf010p1, baselineEdge leaf010p1 leaf010p2, baselineEdge leaf010p2 leaf010p3, baselineEdge leaf010p3 leaf010p4, baselineEdge leaf010p4 leaf010p0]
  vertices := [leaf010p0, leaf010p1, leaf010p2, leaf010p3, leaf010p4]
  implications := [[(23, (1576550742061416950161018386096296542997/1886432409969434583900000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (54897848455030449704558486971852398185221/65157832129336157858400000000000000000000))], [(1, (98578876369086633183846425117095869172911/128152574670317600000000000000000000000000))]]

theorem leaf010_checked : leaf010.Check 11 [point] (25/128) (13/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf010, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf010, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf010p0, leaf010p1, leaf010p2, leaf010p3, leaf010p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf010]
      · intro v hv
        simp only [leaf010, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf010p4, by simp [leaf010], leaf010p1, by simp [leaf010],
            by simp [leaf010], by simp [leaf010], ?_⟩
          norm_num [leaf010p4, leaf010p0, leaf010p1]
        · refine ⟨leaf010p0, by simp [leaf010], leaf010p2, by simp [leaf010],
            by simp [leaf010], by simp [leaf010], ?_⟩
          norm_num [leaf010p0, leaf010p1, leaf010p2]
        · refine ⟨leaf010p1, by simp [leaf010], leaf010p3, by simp [leaf010],
            by simp [leaf010], by simp [leaf010], ?_⟩
          norm_num [leaf010p1, leaf010p2, leaf010p3]
        · refine ⟨leaf010p2, by simp [leaf010], leaf010p4, by simp [leaf010],
            by simp [leaf010], by simp [leaf010], ?_⟩
          norm_num [leaf010p2, leaf010p3, leaf010p4]
        · refine ⟨leaf010p3, by simp [leaf010], leaf010p0, by simp [leaf010],
            by simp [leaf010], by simp [leaf010], ?_⟩
          norm_num [leaf010p3, leaf010p4, leaf010p0]
    · intro v hv
      simp only [leaf010, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf010, point, leaf010p0, leaf010p1, leaf010p2, leaf010p3, leaf010p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
