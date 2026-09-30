import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf013p0 : QPoint := ((22445757149977484728512252433087816761/19978286399200000000000000000000000000), (520567/931090))
def leaf013p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf013p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf013p3 : QPoint := ((520567/931090), (525230266299986672764265932977741361/415049661575000000000000000000000000))
def leaf013p4 : QPoint := ((520567/931090), (520567/931090))

def leaf013 : WallOwnershipLeaf where
  margin := (520567/931090)
  polygon := [baselineEdge leaf013p0 leaf013p1, baselineEdge leaf013p1 leaf013p2, baselineEdge leaf013p2 leaf013p3, baselineEdge leaf013p3 leaf013p4, baselineEdge leaf013p4 leaf013p0]
  vertices := [leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4]
  implications := [[(9, (4841726510253504512010365399341761038917423/5717687426856129166690400000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (10411956952356816410873200124113120984297/10326523326465052893900000000000000000000))], [(0, (293178416127486672764265932977741361/415049661575000000000000000000000000))], [(2, (11276013499017484728512252433087816761/19978286399200000000000000000000000000))]]

theorem leaf013_checked : leaf013.Check 0 [point] (195/256) (451/512) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf013, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf013, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf013]
      · intro v hv
        simp only [leaf013, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf013p4, by simp [leaf013], leaf013p1, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p4, leaf013p0, leaf013p1]
        · refine ⟨leaf013p0, by simp [leaf013], leaf013p2, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p0, leaf013p1, leaf013p2]
        · refine ⟨leaf013p1, by simp [leaf013], leaf013p3, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p1, leaf013p2, leaf013p3]
        · refine ⟨leaf013p2, by simp [leaf013], leaf013p4, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p2, leaf013p3, leaf013p4]
        · refine ⟨leaf013p3, by simp [leaf013], leaf013p0, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p3, leaf013p4, leaf013p0]
    · intro v hv
      simp only [leaf013, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf013, point, leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
