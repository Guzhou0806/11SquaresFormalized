import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf009p0 : QPoint := ((17118543027120915139743/5300000000000000000000), (616865041612296610392552442588063/236256775000000000000000000000000))
def leaf009p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf009p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf009p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf009p4 : QPoint := ((17118543027120915139743/5300000000000000000000), (4124393528471586564890630140877031/2239525600000000000000000000000000))

def leaf009 : WallOwnershipLeaf where
  margin := (343/530)
  polygon := [baselineEdge leaf009p0 leaf009p1, baselineEdge leaf009p1 leaf009p2, baselineEdge leaf009p2 leaf009p3, baselineEdge leaf009p3 leaf009p4, baselineEdge leaf009p4 leaf009p0]
  vertices := [leaf009p0, leaf009p1, leaf009p2, leaf009p3, leaf009p4]
  implications := [[(23, (4958907513615825642808746808342860649/5878118509517316300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (172683926818789748153424646334774360857/203031636360445432800000000000000000000))], [(1, (307221991372253443632421690352524020587/399323091159200000000000000000000000000))]]

theorem leaf009_checked : leaf009.Check 11 [point] (3/16) (25/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf009, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf009, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf009p0, leaf009p1, leaf009p2, leaf009p3, leaf009p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf009]
      · intro v hv
        simp only [leaf009, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf009p4, by simp [leaf009], leaf009p1, by simp [leaf009],
            by simp [leaf009], by simp [leaf009], ?_⟩
          norm_num [leaf009p4, leaf009p0, leaf009p1]
        · refine ⟨leaf009p0, by simp [leaf009], leaf009p2, by simp [leaf009],
            by simp [leaf009], by simp [leaf009], ?_⟩
          norm_num [leaf009p0, leaf009p1, leaf009p2]
        · refine ⟨leaf009p1, by simp [leaf009], leaf009p3, by simp [leaf009],
            by simp [leaf009], by simp [leaf009], ?_⟩
          norm_num [leaf009p1, leaf009p2, leaf009p3]
        · refine ⟨leaf009p2, by simp [leaf009], leaf009p4, by simp [leaf009],
            by simp [leaf009], by simp [leaf009], ?_⟩
          norm_num [leaf009p2, leaf009p3, leaf009p4]
        · refine ⟨leaf009p3, by simp [leaf009], leaf009p0, by simp [leaf009],
            by simp [leaf009], by simp [leaf009], ?_⟩
          norm_num [leaf009p3, leaf009p4, leaf009p0]
    · intro v hv
      simp only [leaf009, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf009, point, leaf009p0, leaf009p1, leaf009p2, leaf009p3, leaf009p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
