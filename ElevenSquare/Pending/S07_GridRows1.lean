import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks0
import ElevenSquare.Pending.S07_GridVertexChecks1
import ElevenSquare.Pending.S07_GridVertexChecks2
import ElevenSquare.Pending.S07_GridVertexChecks3
namespace ElevenSquare.Pending.GridDistance

theorem row_check16 : rowCheck rationalRow16 gridRow16 = true := by
  simp only [rowCheck, rationalRow16, gridRow16, zipCheck, vertex_check31, vertex_check23, vertex_check25, vertex_check32, vertex_check4, vertex_check1, vertex_check30, Bool.true_and]

theorem row_check17 : rowCheck rationalRow17 gridRow17 = true := by
  simp only [rowCheck, rationalRow17, gridRow17, zipCheck, vertex_check25, vertex_check28, vertex_check33, vertex_check32, Bool.true_and]

theorem row_check18 : rowCheck rationalRow18 gridRow18 = true := by
  simp only [rowCheck, rationalRow18, gridRow18, zipCheck, vertex_check9, vertex_check34, vertex_check30, vertex_check0, Bool.true_and]

theorem row_check19 : rowCheck rationalRow19 gridRow19 = true := by
  simp only [rowCheck, rationalRow19, gridRow19, zipCheck, vertex_check34, vertex_check31, vertex_check30, Bool.true_and]

theorem row_check20 : rowCheck rationalRow20 gridRow20 = true := by
  simp only [rowCheck, rationalRow20, gridRow20, zipCheck, vertex_check35, vertex_check36, vertex_check37, Bool.true_and]

theorem row_check21 : rowCheck rationalRow21 gridRow21 = true := by
  simp only [rowCheck, rationalRow21, gridRow21, zipCheck, vertex_check38, vertex_check39, vertex_check35, vertex_check37, Bool.true_and]

theorem row_check22 : rowCheck rationalRow22 gridRow22 = true := by
  simp only [rowCheck, rationalRow22, gridRow22, zipCheck, vertex_check40, vertex_check41, vertex_check28, vertex_check27, Bool.true_and]

theorem row_check23 : rowCheck rationalRow23 gridRow23 = true := by
  simp only [rowCheck, rationalRow23, gridRow23, zipCheck, vertex_check29, vertex_check42, vertex_check43, vertex_check37, vertex_check36, vertex_check40, vertex_check27, Bool.true_and]

theorem row_check24 : rowCheck rationalRow24 gridRow24 = true := by
  simp only [rowCheck, rationalRow24, gridRow24, zipCheck, vertex_check43, vertex_check38, vertex_check37, Bool.true_and]

theorem row_check25 : rowCheck rationalRow25 gridRow25 = true := by
  simp only [rowCheck, rationalRow25, gridRow25, zipCheck, vertex_check41, vertex_check44, vertex_check33, vertex_check28, Bool.true_and]

theorem row_check26 : rowCheck rationalRow26 gridRow26 = true := by
  simp only [rowCheck, rationalRow26, gridRow26, zipCheck, vertex_check45, vertex_check46, vertex_check47, vertex_check48, Bool.true_and]

theorem row_check27 : rowCheck rationalRow27 gridRow27 = true := by
  simp only [rowCheck, rationalRow27, gridRow27, zipCheck, vertex_check49, vertex_check50, vertex_check51, vertex_check52, vertex_check53, vertex_check54, Bool.true_and]

theorem row_check28 : rowCheck rationalRow28 gridRow28 = true := by
  simp only [rowCheck, rationalRow28, gridRow28, zipCheck, vertex_check55, vertex_check45, vertex_check48, vertex_check53, vertex_check52, Bool.true_and]

theorem row_check29 : rowCheck rationalRow29 gridRow29 = true := by
  simp only [rowCheck, rationalRow29, gridRow29, zipCheck, vertex_check51, vertex_check56, vertex_check55, vertex_check52, Bool.true_and]

theorem row_check30 : rowCheck rationalRow30 gridRow30 = true := by
  simp only [rowCheck, rationalRow30, gridRow30, zipCheck, vertex_check57, vertex_check44, vertex_check41, vertex_check40, vertex_check58, Bool.true_and]

theorem row_check31 : rowCheck rationalRow31 gridRow31 = true := by
  simp only [rowCheck, rationalRow31, gridRow31, zipCheck, vertex_check40, vertex_check36, vertex_check35, vertex_check54, vertex_check53, vertex_check58, Bool.true_and]

theorem aligned_chunk1 : ArrayAligned Row recordedOverlayVerticesChunk1 gridChunk1 := by
  have heq : recordedOverlayVerticesChunk1 = rationalChunk1 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow16, rationalRow17, rationalRow18, rationalRow19, rationalRow20, rationalRow21, rationalRow22, rationalRow23, rationalRow24, rationalRow25, rationalRow26, rationalRow27, rationalRow28, rationalRow29, rationalRow30, rationalRow31] [gridRow16, gridRow17, gridRow18, gridRow19, gridRow20, gridRow21, gridRow22, gridRow23, gridRow24, gridRow25, gridRow26, gridRow27, gridRow28, gridRow29, gridRow30, gridRow31]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow16 gridRow16 row_check16) (List.Forall₂.cons (rowCheck_sound rationalRow17 gridRow17 row_check17) (List.Forall₂.cons (rowCheck_sound rationalRow18 gridRow18 row_check18) (List.Forall₂.cons (rowCheck_sound rationalRow19 gridRow19 row_check19) (List.Forall₂.cons (rowCheck_sound rationalRow20 gridRow20 row_check20) (List.Forall₂.cons (rowCheck_sound rationalRow21 gridRow21 row_check21) (List.Forall₂.cons (rowCheck_sound rationalRow22 gridRow22 row_check22) (List.Forall₂.cons (rowCheck_sound rationalRow23 gridRow23 row_check23) (List.Forall₂.cons (rowCheck_sound rationalRow24 gridRow24 row_check24) (List.Forall₂.cons (rowCheck_sound rationalRow25 gridRow25 row_check25) (List.Forall₂.cons (rowCheck_sound rationalRow26 gridRow26 row_check26) (List.Forall₂.cons (rowCheck_sound rationalRow27 gridRow27 row_check27) (List.Forall₂.cons (rowCheck_sound rationalRow28 gridRow28 row_check28) (List.Forall₂.cons (rowCheck_sound rationalRow29 gridRow29 row_check29) (List.Forall₂.cons (rowCheck_sound rationalRow30 gridRow30 row_check30) (List.Forall₂.cons (rowCheck_sound rationalRow31 gridRow31 row_check31) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk1
