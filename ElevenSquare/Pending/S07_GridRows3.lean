import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks0
import ElevenSquare.Pending.S07_GridVertexChecks2
import ElevenSquare.Pending.S07_GridVertexChecks4
import ElevenSquare.Pending.S07_GridVertexChecks5
import ElevenSquare.Pending.S07_GridVertexChecks6
namespace ElevenSquare.Pending.GridDistance

theorem row_check48 : rowCheck rationalRow48 gridRow48 = true := by
  simp only [rowCheck, rationalRow48, gridRow48, zipCheck, vertex_check80, vertex_check82, vertex_check83, vertex_check81, Bool.true_and]

theorem row_check49 : rowCheck rationalRow49 gridRow49 = true := by
  simp only [rowCheck, rationalRow49, gridRow49, zipCheck, vertex_check75, vertex_check78, vertex_check84, vertex_check80, Bool.true_and]

theorem row_check50 : rowCheck rationalRow50 gridRow50 = true := by
  simp only [rowCheck, rationalRow50, gridRow50, zipCheck, vertex_check84, vertex_check85, vertex_check82, vertex_check80, Bool.true_and]

theorem row_check51 : rowCheck rationalRow51 gridRow51 = true := by
  simp only [rowCheck, rationalRow51, gridRow51, zipCheck, vertex_check78, vertex_check71, vertex_check70, vertex_check85, vertex_check84, Bool.true_and]

theorem row_check52 : rowCheck rationalRow52 gridRow52 = true := by
  simp only [rowCheck, rationalRow52, gridRow52, zipCheck, vertex_check86, vertex_check87, vertex_check83, vertex_check82, vertex_check85, Bool.true_and]

theorem row_check53 : rowCheck rationalRow53 gridRow53 = true := by
  simp only [rowCheck, rationalRow53, gridRow53, zipCheck, vertex_check70, vertex_check72, vertex_check86, vertex_check85, Bool.true_and]

theorem row_check54 : rowCheck rationalRow54 gridRow54 = true := by
  simp only [rowCheck, rationalRow54, gridRow54, zipCheck, vertex_check88, vertex_check89, vertex_check90, vertex_check91, Bool.true_and]

theorem row_check55 : rowCheck rationalRow55 gridRow55 = true := by
  simp only [rowCheck, rationalRow55, gridRow55, zipCheck, vertex_check92, vertex_check93, vertex_check94, vertex_check95, vertex_check96, Bool.true_and]

theorem row_check56 : rowCheck rationalRow56 gridRow56 = true := by
  simp only [rowCheck, rationalRow56, gridRow56, zipCheck, vertex_check97, vertex_check88, vertex_check91, vertex_check95, vertex_check94, Bool.true_and]

theorem row_check57 : rowCheck rationalRow57 gridRow57 = true := by
  simp only [rowCheck, rationalRow57, gridRow57, zipCheck, vertex_check93, vertex_check98, vertex_check97, vertex_check94, Bool.true_and]

theorem row_check58 : rowCheck rationalRow58 gridRow58 = true := by
  simp only [rowCheck, rationalRow58, gridRow58, zipCheck, vertex_check3, vertex_check2, vertex_check99, vertex_check100, Bool.true_and]

theorem row_check59 : rowCheck rationalRow59 gridRow59 = true := by
  simp only [rowCheck, rationalRow59, gridRow59, zipCheck, vertex_check2, vertex_check4, vertex_check32, vertex_check96, vertex_check95, vertex_check99, Bool.true_and]

theorem row_check60 : rowCheck rationalRow60 gridRow60 = true := by
  simp only [rowCheck, rationalRow60, gridRow60, zipCheck, vertex_check95, vertex_check91, vertex_check90, vertex_check101, vertex_check100, vertex_check99, Bool.true_and]

theorem row_check61 : rowCheck rationalRow61 gridRow61 = true := by
  simp only [rowCheck, rationalRow61, gridRow61, zipCheck, vertex_check32, vertex_check33, vertex_check44, vertex_check92, vertex_check96, Bool.true_and]

theorem row_check62 : rowCheck rationalRow62 gridRow62 = true := by
  simp only [rowCheck, rationalRow62, gridRow62, zipCheck, vertex_check10, vertex_check3, vertex_check100, vertex_check102, Bool.true_and]

theorem row_check63 : rowCheck rationalRow63 gridRow63 = true := by
  simp only [rowCheck, rationalRow63, gridRow63, zipCheck, vertex_check100, vertex_check101, vertex_check102, Bool.true_and]

theorem aligned_chunk3 : ArrayAligned Row recordedOverlayVerticesChunk3 gridChunk3 := by
  have heq : recordedOverlayVerticesChunk3 = rationalChunk3 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow48, rationalRow49, rationalRow50, rationalRow51, rationalRow52, rationalRow53, rationalRow54, rationalRow55, rationalRow56, rationalRow57, rationalRow58, rationalRow59, rationalRow60, rationalRow61, rationalRow62, rationalRow63] [gridRow48, gridRow49, gridRow50, gridRow51, gridRow52, gridRow53, gridRow54, gridRow55, gridRow56, gridRow57, gridRow58, gridRow59, gridRow60, gridRow61, gridRow62, gridRow63]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow48 gridRow48 row_check48) (List.Forall₂.cons (rowCheck_sound rationalRow49 gridRow49 row_check49) (List.Forall₂.cons (rowCheck_sound rationalRow50 gridRow50 row_check50) (List.Forall₂.cons (rowCheck_sound rationalRow51 gridRow51 row_check51) (List.Forall₂.cons (rowCheck_sound rationalRow52 gridRow52 row_check52) (List.Forall₂.cons (rowCheck_sound rationalRow53 gridRow53 row_check53) (List.Forall₂.cons (rowCheck_sound rationalRow54 gridRow54 row_check54) (List.Forall₂.cons (rowCheck_sound rationalRow55 gridRow55 row_check55) (List.Forall₂.cons (rowCheck_sound rationalRow56 gridRow56 row_check56) (List.Forall₂.cons (rowCheck_sound rationalRow57 gridRow57 row_check57) (List.Forall₂.cons (rowCheck_sound rationalRow58 gridRow58 row_check58) (List.Forall₂.cons (rowCheck_sound rationalRow59 gridRow59 row_check59) (List.Forall₂.cons (rowCheck_sound rationalRow60 gridRow60 row_check60) (List.Forall₂.cons (rowCheck_sound rationalRow61 gridRow61 row_check61) (List.Forall₂.cons (rowCheck_sound rationalRow62 gridRow62 row_check62) (List.Forall₂.cons (rowCheck_sound rationalRow63 gridRow63 row_check63) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk3
