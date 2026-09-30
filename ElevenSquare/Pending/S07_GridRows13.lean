import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks11
import ElevenSquare.Pending.S07_GridVertexChecks12
import ElevenSquare.Pending.S07_GridVertexChecks13
import ElevenSquare.Pending.S07_GridVertexChecks14
import ElevenSquare.Pending.S07_GridVertexChecks16
import ElevenSquare.Pending.S07_GridVertexChecks17
namespace ElevenSquare.Pending.GridDistance

theorem row_check208 : rowCheck rationalRow208 gridRow208 = true := by
  simp only [rowCheck, rationalRow208, gridRow208, zipCheck, vertex_check187, vertex_check186, vertex_check265, Bool.true_and]

theorem row_check209 : rowCheck rationalRow209 gridRow209 = true := by
  simp only [rowCheck, rationalRow209, gridRow209, zipCheck, vertex_check266, vertex_check192, vertex_check187, vertex_check265, Bool.true_and]

theorem row_check210 : rowCheck rationalRow210 gridRow210 = true := by
  simp only [rowCheck, rationalRow210, gridRow210, zipCheck, vertex_check265, vertex_check186, vertex_check193, vertex_check267, Bool.true_and]

theorem row_check211 : rowCheck rationalRow211 gridRow211 = true := by
  simp only [rowCheck, rationalRow211, gridRow211, zipCheck, vertex_check227, vertex_check268, vertex_check269, vertex_check228, Bool.true_and]

theorem row_check212 : rowCheck rationalRow212 gridRow212 = true := by
  simp only [rowCheck, rationalRow212, gridRow212, zipCheck, vertex_check268, vertex_check270, vertex_check266, vertex_check265, vertex_check267, vertex_check269, Bool.true_and]

theorem row_check213 : rowCheck rationalRow213 gridRow213 = true := by
  simp only [rowCheck, rationalRow213, gridRow213, zipCheck, vertex_check193, vertex_check195, vertex_check230, vertex_check267, Bool.true_and]

theorem row_check214 : rowCheck rationalRow214 gridRow214 = true := by
  simp only [rowCheck, rationalRow214, gridRow214, zipCheck, vertex_check232, vertex_check228, vertex_check269, Bool.true_and]

theorem row_check215 : rowCheck rationalRow215 gridRow215 = true := by
  simp only [rowCheck, rationalRow215, gridRow215, zipCheck, vertex_check230, vertex_check232, vertex_check269, vertex_check267, Bool.true_and]

theorem row_check216 : rowCheck rationalRow216 gridRow216 = true := by
  simp only [rowCheck, rationalRow216, gridRow216, zipCheck, vertex_check271, vertex_check258, vertex_check259, vertex_check207, vertex_check192, vertex_check266, Bool.true_and]

theorem row_check217 : rowCheck rationalRow217 gridRow217 = true := by
  simp only [rowCheck, rationalRow217, gridRow217, zipCheck, vertex_check270, vertex_check272, vertex_check271, vertex_check266, Bool.true_and]

theorem row_check218 : rowCheck rationalRow218 gridRow218 = true := by
  simp only [rowCheck, rationalRow218, gridRow218, zipCheck, vertex_check262, vertex_check215, vertex_check214, Bool.true_and]

theorem row_check219 : rowCheck rationalRow219 gridRow219 = true := by
  simp only [rowCheck, rationalRow219, gridRow219, zipCheck, vertex_check259, vertex_check262, vertex_check214, vertex_check207, Bool.true_and]

theorem aligned_chunk13 : ArrayAligned Row recordedOverlayVerticesChunk13 gridChunk13 := by
  have heq : recordedOverlayVerticesChunk13 = rationalChunk13 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow208, rationalRow209, rationalRow210, rationalRow211, rationalRow212, rationalRow213, rationalRow214, rationalRow215, rationalRow216, rationalRow217, rationalRow218, rationalRow219] [gridRow208, gridRow209, gridRow210, gridRow211, gridRow212, gridRow213, gridRow214, gridRow215, gridRow216, gridRow217, gridRow218, gridRow219]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow208 gridRow208 row_check208) (List.Forall₂.cons (rowCheck_sound rationalRow209 gridRow209 row_check209) (List.Forall₂.cons (rowCheck_sound rationalRow210 gridRow210 row_check210) (List.Forall₂.cons (rowCheck_sound rationalRow211 gridRow211 row_check211) (List.Forall₂.cons (rowCheck_sound rationalRow212 gridRow212 row_check212) (List.Forall₂.cons (rowCheck_sound rationalRow213 gridRow213 row_check213) (List.Forall₂.cons (rowCheck_sound rationalRow214 gridRow214 row_check214) (List.Forall₂.cons (rowCheck_sound rationalRow215 gridRow215 row_check215) (List.Forall₂.cons (rowCheck_sound rationalRow216 gridRow216 row_check216) (List.Forall₂.cons (rowCheck_sound rationalRow217 gridRow217 row_check217) (List.Forall₂.cons (rowCheck_sound rationalRow218 gridRow218 row_check218) (List.Forall₂.cons (rowCheck_sound rationalRow219 gridRow219 row_check219) List.Forall₂.nil))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk13
