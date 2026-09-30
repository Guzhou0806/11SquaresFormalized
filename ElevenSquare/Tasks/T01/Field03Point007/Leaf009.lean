import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf009p0 : QPoint := ((70144029724084945561199856049795156713/60293189093600000000000000000000000000), (1914823/2809970))
def leaf009p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf009p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf009p3 : QPoint := ((1914823/2809970), (1586200251288244907439027745641628513/1252593301975000000000000000000000000))
def leaf009p4 : QPoint := ((1914823/2809970), (1914823/2809970))

def leaf009 : WallOwnershipLeaf where
  margin := (1914823/2809970)
  polygon := [baselineEdge leaf009p0 leaf009p1, baselineEdge leaf009p1 leaf009p2, baselineEdge leaf009p2 leaf009p3, baselineEdge leaf009p3 leaf009p4, baselineEdge leaf009p4 leaf009p0]
  vertices := [leaf009p0, leaf009p1, leaf009p2, leaf009p3, leaf009p4]
  implications := [[(9, (10676435995963619815544540765327055672949759/17255614536557064595823200000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (24294747174713465625515649564224883279001/31164786166393157138700000000000000000000))], [(0, (732634389635744907439027745641628513/1252593301975000000000000000000000000))], [(2, (29057902391844945561199856049795156713/60293189093600000000000000000000000000))]]

theorem leaf009_checked : leaf009.Check 0 [point] (1133/2048) (597/1024) := by
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
end ElevenSquare.Tasks.T01.Field03Point007
