import ElevenSquare.Tasks.T01.Field03Point007Early.Data

namespace ElevenSquare.Tasks.T01.Field03Point007Early
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf004p0 : QPoint := ((2497896449351019185227690296004232781/2250612143200000000000000000000000000), (271279/524450))
def leaf004p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf004p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf004p3 : QPoint := ((271279/524450), (59154821376143833685512521571529381/46756553075000000000000000000000000))
def leaf004p4 : QPoint := ((271279/524450), (271279/524450))

def leaf004 : WallOwnershipLeaf where
  margin := (271279/524450)
  polygon := [baselineEdge leaf004p0 leaf004p1, baselineEdge leaf004p1 leaf004p2, baselineEdge leaf004p2 leaf004p3, baselineEdge leaf004p3 leaf004p4, baselineEdge leaf004p4 leaf004p0]
  vertices := [leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4]
  implications := [[(9, (595662842749077887650610818220534336500283/644114139560020393618400000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (1263907380749986625800395193824684251837/1163312925402398691900000000000000000000))], [(0, (34969349049643833685512521571529381/46756553075000000000000000000000000))], [(2, (1333736259447019185227690296004232781/2250612143200000000000000000000000000))]]

theorem leaf004_checked : leaf004.Check 0 [point] (9/512) (3/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf004, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf004, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf004]
      · intro v hv
        simp only [leaf004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf004p4, by simp [leaf004], leaf004p1, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p4, leaf004p0, leaf004p1]
        · refine ⟨leaf004p0, by simp [leaf004], leaf004p2, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p0, leaf004p1, leaf004p2]
        · refine ⟨leaf004p1, by simp [leaf004], leaf004p3, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p1, leaf004p2, leaf004p3]
        · refine ⟨leaf004p2, by simp [leaf004], leaf004p4, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p2, leaf004p3, leaf004p4]
        · refine ⟨leaf004p3, by simp [leaf004], leaf004p0, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p3, leaf004p4, leaf004p0]
    · intro v hv
      simp only [leaf004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf004, point, leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007Early
