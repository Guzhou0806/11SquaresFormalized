import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf000p0 : QPoint := ((197084873078512227197247948614689209/176160984800000000000000000000000000), (4471/8210))
def leaf000p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf000p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf000p3 : QPoint := ((4471/8210), (4630904688995146101230410926706609/3659751175000000000000000000000000))
def leaf000p4 : QPoint := ((4471/8210), (4471/8210))

def leaf000 : WallOwnershipLeaf where
  margin := (4471/8210)
  polygon := [baselineEdge leaf000p0 leaf000p1, baselineEdge leaf000p1 leaf000p2, baselineEdge leaf000p2 leaf000p3, baselineEdge leaf000p3 leaf000p4, baselineEdge leaf000p4 leaf000p0]
  vertices := [leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4]
  implications := [[(9, (44056673018101544694932927996859442298287/50416408483056224917600000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (94279376098207412315961908106594124393/91055382949315409100000000000000000000))], [(0, (2637878196495146101230410926706609/3659751175000000000000000000000000))], [(2, (101151162598512227197247948614689209/176160984800000000000000000000000000))]]

theorem leaf000_checked : leaf000.Check 0 [point] (3/64) (253/4096) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf000, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf000, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf000]
      · intro v hv
        simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf000p4, by simp [leaf000], leaf000p1, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p4, leaf000p0, leaf000p1]
        · refine ⟨leaf000p0, by simp [leaf000], leaf000p2, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p0, leaf000p1, leaf000p2]
        · refine ⟨leaf000p1, by simp [leaf000], leaf000p3, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p1, leaf000p2, leaf000p3]
        · refine ⟨leaf000p2, by simp [leaf000], leaf000p4, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p2, leaf000p3, leaf000p4]
        · refine ⟨leaf000p3, by simp [leaf000], leaf000p0, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p3, leaf000p4, leaf000p0]
    · intro v hv
      simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf000, point, leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
