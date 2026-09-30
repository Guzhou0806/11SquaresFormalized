import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf014p0 : QPoint := ((1385737819248858006015651/432100000000000000000000), (50288821000881767047287152913641891/19261613675000000000000000000000000))
def leaf014p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf014p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf014p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf014p4 : QPoint := ((1385737819248858006015651/432100000000000000000000), (336350416124032557488536091296785867/182584719200000000000000000000000000))

def leaf014 : WallOwnershipLeaf where
  margin := (5791/8642)
  polygon := [baselineEdge leaf014p0 leaf014p1, baselineEdge leaf014p1 leaf014p2, baselineEdge leaf014p2 leaf014p3, baselineEdge leaf014p3 leaf014p4, baselineEdge leaf014p4 leaf014p0]
  vertices := [leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4]
  implications := [[(23, (383748704055563445331633867148103789893/479233020370270259100000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (13360038654895721769263167864387924778549/16552824541763862549600000000000000000000))], [(1, (25024933918430496489352719321004835716159/32556133526394400000000000000000000000000))]]

theorem leaf014_checked : leaf014.Check 11 [point] (15/64) (1/4) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf014, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf014, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf014]
      · intro v hv
        simp only [leaf014, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf014p4, by simp [leaf014], leaf014p1, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p4, leaf014p0, leaf014p1]
        · refine ⟨leaf014p0, by simp [leaf014], leaf014p2, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p0, leaf014p1, leaf014p2]
        · refine ⟨leaf014p1, by simp [leaf014], leaf014p3, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p1, leaf014p2, leaf014p3]
        · refine ⟨leaf014p2, by simp [leaf014], leaf014p4, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p2, leaf014p3, leaf014p4]
        · refine ⟨leaf014p3, by simp [leaf014], leaf014p0, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p3, leaf014p4, leaf014p0]
    · intro v hv
      simp only [leaf014, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf014, point, leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
