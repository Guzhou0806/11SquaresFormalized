import ElevenSquare.Tasks.T01.Field03Point007Early.Data

namespace ElevenSquare.Tasks.T01.Field03Point007Early
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf001p0 : QPoint := ((49732575359030583131699449500154417593/44998725029600000000000000000000000000), (1054711/2097170))
def leaf001p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf001p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf001p3 : QPoint := ((1054711/2097170), (1182645850749713830586769900506857393/934850227975000000000000000000000000))
def leaf001p4 : QPoint := ((1054711/2097170), (1054711/2097170))

def leaf001 : WallOwnershipLeaf where
  margin := (1054711/2097170)
  polygon := [baselineEdge leaf001p0 leaf001p1, baselineEdge leaf001p1 leaf001p2, baselineEdge leaf001p2 leaf001p3, baselineEdge leaf001p3 leaf001p4, baselineEdge leaf001p4 leaf001p0]
  vertices := [leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4]
  implications := [[(9, (12254019028778905575234164263967565968903599/12878414053399637419055200000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (25894202017304878987413621781230937862761/23259271310574396650700000000000000000000))], [(0, (712489965057213830586769900506857393/934850227975000000000000000000000000))], [(2, (27101767997350583131699449500154417593/44998725029600000000000000000000000000))]]

theorem leaf001_checked : leaf001.Check 0 [point] (3/1024) (3/512) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf001, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf001, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf001]
      · intro v hv
        simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf001p4, by simp [leaf001], leaf001p1, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p4, leaf001p0, leaf001p1]
        · refine ⟨leaf001p0, by simp [leaf001], leaf001p2, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p0, leaf001p1, leaf001p2]
        · refine ⟨leaf001p1, by simp [leaf001], leaf001p3, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p1, leaf001p2, leaf001p3]
        · refine ⟨leaf001p2, by simp [leaf001], leaf001p4, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p2, leaf001p3, leaf001p4]
        · refine ⟨leaf001p3, by simp [leaf001], leaf001p0, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p3, leaf001p4, leaf001p0]
    · intro v hv
      simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf001, point, leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007Early
