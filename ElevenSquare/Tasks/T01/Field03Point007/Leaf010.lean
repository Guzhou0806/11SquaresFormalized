import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf010p0 : QPoint := ((1436565772318884907702401108566670255141/1237918000335200000000000000000000000000), (7759759/11538658))
def leaf010p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf010p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf010p3 : QPoint := ((7759759/11538658), (32565657791397024678520761804342647741/25717793650075000000000000000000000000))
def leaf010p4 : QPoint := ((7759759/11538658), (7759759/11538658))

def leaf010 : WallOwnershipLeaf where
  margin := (7759759/11538658)
  polygon := [baselineEdge leaf010p0 leaf010p1, baselineEdge leaf010p1 leaf010p2, baselineEdge leaf010p2 leaf010p3, baselineEdge leaf010p3 leaf010p4, baselineEdge leaf010p4 leaf010p0]
  vertices := [leaf010p0, leaf010p1, leaf010p2, leaf010p3, leaf010p4]
  implications := [[(9, (225107903445887088331294390435070754415753763/354286050593352359375922400000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (509502419674799601132078196509998261985557/639864143064057149655900000000000000000000))], [(0, (15270415941234524678520761804342647741/25717793650075000000000000000000000000))], [(2, (604064683859284907702401108566670255141/1237918000335200000000000000000000000000))]]

theorem leaf010_checked : leaf010.Check 0 [point] (597/1024) (1255/2048) := by
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
end ElevenSquare.Tasks.T01.Field03Point007
