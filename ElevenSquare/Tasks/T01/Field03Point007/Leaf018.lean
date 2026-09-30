import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf018p0 : QPoint := ((1/2), (1/2))
def leaf018p1 : QPoint := ((236937085552390045307244760797429/214568800000000000000000000000000), (1/2))
def leaf018p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf018p3 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf018p4 : QPoint := ((1/2), (5639153939092747991754459106829/4457675000000000000000000000000))

def leaf018 : WallOwnershipLeaf where
  margin := (1/2)
  polygon := [baselineEdge leaf018p0 leaf018p1, baselineEdge leaf018p1 leaf018p2, baselineEdge leaf018p2 leaf018p3, baselineEdge leaf018p3 leaf018p4, baselineEdge leaf018p4 leaf018p0]
  vertices := [leaf018p0, leaf018p1, leaf018p2, leaf018p3, leaf018p4]
  implications := [[(2, (129652685552390045307244760797429/214568800000000000000000000000000))], [(9, (58765614008656790127811118144773985747/61408536520165925600000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (124077759535770295147334845440431333/110907896405987100000000000000000000))], [(0, (3410316439092747991754459106829/4457675000000000000000000000000))]]

theorem leaf018_checked : leaf018.Check 0 [point] (8131/8192) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf018, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf018, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf018p0, leaf018p1, leaf018p2, leaf018p3, leaf018p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf018]
      · intro v hv
        simp only [leaf018, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf018p4, by simp [leaf018], leaf018p1, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p4, leaf018p0, leaf018p1]
        · refine ⟨leaf018p0, by simp [leaf018], leaf018p2, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p0, leaf018p1, leaf018p2]
        · refine ⟨leaf018p1, by simp [leaf018], leaf018p3, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p1, leaf018p2, leaf018p3]
        · refine ⟨leaf018p2, by simp [leaf018], leaf018p4, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p2, leaf018p3, leaf018p4]
        · refine ⟨leaf018p3, by simp [leaf018], leaf018p0, by simp [leaf018],
            by simp [leaf018], by simp [leaf018], ?_⟩
          norm_num [leaf018p3, leaf018p4, leaf018p0]
    · intro v hv
      simp only [leaf018, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf018, point, leaf018p0, leaf018p1, leaf018p2, leaf018p3, leaf018p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
