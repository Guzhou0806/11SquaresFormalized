import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks0
import ElevenSquare.Pending.S07_GridVertexChecks1
import ElevenSquare.Pending.S07_GridVertexChecks2
import ElevenSquare.Pending.S07_GridVertexChecks3
import ElevenSquare.Pending.S07_GridVertexChecks4
import ElevenSquare.Pending.S07_GridVertexChecks5
import ElevenSquare.Pending.S07_GridVertexChecks6
import ElevenSquare.Pending.S07_GridVertexChecks7
namespace ElevenSquare.Pending.GridDistance

theorem row_check64 : rowCheck rationalRow64 gridRow64 = true := by
  simp only [rowCheck, rationalRow64, gridRow64, zipCheck, vertex_check93, vertex_check92, vertex_check103, Bool.true_and]

theorem row_check65 : rowCheck rationalRow65 gridRow65 = true := by
  simp only [rowCheck, rationalRow65, gridRow65, zipCheck, vertex_check47, vertex_check46, vertex_check104, vertex_check98, vertex_check93, vertex_check103, Bool.true_and]

theorem row_check66 : rowCheck rationalRow66 gridRow66 = true := by
  simp only [rowCheck, rationalRow66, gridRow66, zipCheck, vertex_check44, vertex_check57, vertex_check103, vertex_check92, Bool.true_and]

theorem row_check67 : rowCheck rationalRow67 gridRow67 = true := by
  simp only [rowCheck, rationalRow67, gridRow67, zipCheck, vertex_check57, vertex_check47, vertex_check103, Bool.true_and]

theorem row_check68 : rowCheck rationalRow68 gridRow68 = true := by
  simp only [rowCheck, rationalRow68, gridRow68, zipCheck, vertex_check68, vertex_check67, vertex_check89, vertex_check88, vertex_check105, Bool.true_and]

theorem row_check69 : rowCheck rationalRow69 gridRow69 = true := by
  simp only [rowCheck, rationalRow69, gridRow69, zipCheck, vertex_check88, vertex_check97, vertex_check106, vertex_check105, Bool.true_and]

theorem row_check70 : rowCheck rationalRow70 gridRow70 = true := by
  simp only [rowCheck, rationalRow70, gridRow70, zipCheck, vertex_check97, vertex_check98, vertex_check104, vertex_check107, vertex_check106, Bool.true_and]

theorem row_check71 : rowCheck rationalRow71 gridRow71 = true := by
  simp only [rowCheck, rationalRow71, gridRow71, zipCheck, vertex_check67, vertex_check17, vertex_check16, vertex_check108, vertex_check90, vertex_check89, Bool.true_and]

theorem row_check72 : rowCheck rationalRow72 gridRow72 = true := by
  simp only [rowCheck, rationalRow72, gridRow72, zipCheck, vertex_check16, vertex_check21, vertex_check108, Bool.true_and]

theorem row_check73 : rowCheck rationalRow73 gridRow73 = true := by
  simp only [rowCheck, rationalRow73, gridRow73, zipCheck, vertex_check22, vertex_check10, vertex_check102, Bool.true_and]

theorem row_check74 : rowCheck rationalRow74 gridRow74 = true := by
  simp only [rowCheck, rationalRow74, gridRow74, zipCheck, vertex_check21, vertex_check22, vertex_check102, vertex_check101, vertex_check90, vertex_check108, Bool.true_and]

theorem row_check75 : rowCheck rationalRow75 gridRow75 = true := by
  simp only [rowCheck, rationalRow75, gridRow75, zipCheck, vertex_check109, vertex_check110, vertex_check111, Bool.true_and]

theorem row_check76 : rowCheck rationalRow76 gridRow76 = true := by
  simp only [rowCheck, rationalRow76, gridRow76, zipCheck, vertex_check112, vertex_check113, vertex_check109, vertex_check111, vertex_check114, Bool.true_and]

theorem row_check77 : rowCheck rationalRow77 gridRow77 = true := by
  simp only [rowCheck, rationalRow77, gridRow77, zipCheck, vertex_check104, vertex_check46, vertex_check45, vertex_check115, vertex_check116, Bool.true_and]

theorem row_check78 : rowCheck rationalRow78 gridRow78 = true := by
  simp only [rowCheck, rationalRow78, gridRow78, zipCheck, vertex_check45, vertex_check55, vertex_check117, vertex_check115, Bool.true_and]

theorem row_check79 : rowCheck rationalRow79 gridRow79 = true := by
  simp only [rowCheck, rationalRow79, gridRow79, zipCheck, vertex_check55, vertex_check56, vertex_check112, vertex_check114, vertex_check117, Bool.true_and]

theorem aligned_chunk4 : ArrayAligned Row recordedOverlayVerticesChunk4 gridChunk4 := by
  have heq : recordedOverlayVerticesChunk4 = rationalChunk4 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow64, rationalRow65, rationalRow66, rationalRow67, rationalRow68, rationalRow69, rationalRow70, rationalRow71, rationalRow72, rationalRow73, rationalRow74, rationalRow75, rationalRow76, rationalRow77, rationalRow78, rationalRow79] [gridRow64, gridRow65, gridRow66, gridRow67, gridRow68, gridRow69, gridRow70, gridRow71, gridRow72, gridRow73, gridRow74, gridRow75, gridRow76, gridRow77, gridRow78, gridRow79]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow64 gridRow64 row_check64) (List.Forall₂.cons (rowCheck_sound rationalRow65 gridRow65 row_check65) (List.Forall₂.cons (rowCheck_sound rationalRow66 gridRow66 row_check66) (List.Forall₂.cons (rowCheck_sound rationalRow67 gridRow67 row_check67) (List.Forall₂.cons (rowCheck_sound rationalRow68 gridRow68 row_check68) (List.Forall₂.cons (rowCheck_sound rationalRow69 gridRow69 row_check69) (List.Forall₂.cons (rowCheck_sound rationalRow70 gridRow70 row_check70) (List.Forall₂.cons (rowCheck_sound rationalRow71 gridRow71 row_check71) (List.Forall₂.cons (rowCheck_sound rationalRow72 gridRow72 row_check72) (List.Forall₂.cons (rowCheck_sound rationalRow73 gridRow73 row_check73) (List.Forall₂.cons (rowCheck_sound rationalRow74 gridRow74 row_check74) (List.Forall₂.cons (rowCheck_sound rationalRow75 gridRow75 row_check75) (List.Forall₂.cons (rowCheck_sound rationalRow76 gridRow76 row_check76) (List.Forall₂.cons (rowCheck_sound rationalRow77 gridRow77 row_check77) (List.Forall₂.cons (rowCheck_sound rationalRow78 gridRow78 row_check78) (List.Forall₂.cons (rowCheck_sound rationalRow79 gridRow79 row_check79) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk4
