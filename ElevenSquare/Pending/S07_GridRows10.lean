import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks6
import ElevenSquare.Pending.S07_GridVertexChecks7
import ElevenSquare.Pending.S07_GridVertexChecks8
import ElevenSquare.Pending.S07_GridVertexChecks9
import ElevenSquare.Pending.S07_GridVertexChecks11
import ElevenSquare.Pending.S07_GridVertexChecks12
import ElevenSquare.Pending.S07_GridVertexChecks13
import ElevenSquare.Pending.S07_GridVertexChecks14
namespace ElevenSquare.Pending.GridDistance

theorem row_check160 : rowCheck rationalRow160 gridRow160 = true := by
  simp only [rowCheck, rationalRow160, gridRow160, zipCheck, vertex_check214, vertex_check215, vertex_check210, vertex_check209, vertex_check212, vertex_check211, Bool.true_and]

theorem row_check161 : rowCheck rationalRow161 gridRow161 = true := by
  simp only [rowCheck, rationalRow161, gridRow161, zipCheck, vertex_check206, vertex_check207, vertex_check214, vertex_check211, Bool.true_and]

theorem row_check162 : rowCheck rationalRow162 gridRow162 = true := by
  simp only [rowCheck, rationalRow162, gridRow162, zipCheck, vertex_check205, vertex_check198, vertex_check197, vertex_check216, Bool.true_and]

theorem row_check163 : rowCheck rationalRow163 gridRow163 = true := by
  simp only [rowCheck, rationalRow163, gridRow163, zipCheck, vertex_check197, vertex_check199, vertex_check213, vertex_check212, vertex_check216, Bool.true_and]

theorem row_check164 : rowCheck rationalRow164 gridRow164 = true := by
  simp only [rowCheck, rationalRow164, gridRow164, zipCheck, vertex_check204, vertex_check205, vertex_check216, vertex_check212, vertex_check209, Bool.true_and]

theorem row_check165 : rowCheck rationalRow165 gridRow165 = true := by
  simp only [rowCheck, rationalRow165, gridRow165, zipCheck, vertex_check199, vertex_check196, vertex_check190, vertex_check213, Bool.true_and]

theorem row_check166 : rowCheck rationalRow166 gridRow166 = true := by
  simp only [rowCheck, rationalRow166, gridRow166, zipCheck, vertex_check217, vertex_check110, vertex_check109, vertex_check218, Bool.true_and]

theorem row_check167 : rowCheck rationalRow167 gridRow167 = true := by
  simp only [rowCheck, rationalRow167, gridRow167, zipCheck, vertex_check109, vertex_check113, vertex_check141, vertex_check219, vertex_check218, Bool.true_and]

theorem row_check168 : rowCheck rationalRow168 gridRow168 = true := by
  simp only [rowCheck, rationalRow168, gridRow168, zipCheck, vertex_check220, vertex_check221, vertex_check217, vertex_check218, vertex_check222, Bool.true_and]

theorem row_check169 : rowCheck rationalRow169 gridRow169 = true := by
  simp only [rowCheck, rationalRow169, gridRow169, zipCheck, vertex_check222, vertex_check218, vertex_check219, vertex_check223, Bool.true_and]

theorem row_check170 : rowCheck rationalRow170 gridRow170 = true := by
  simp only [rowCheck, rationalRow170, gridRow170, zipCheck, vertex_check224, vertex_check220, vertex_check222, vertex_check223, Bool.true_and]

theorem row_check171 : rowCheck rationalRow171 gridRow171 = true := by
  simp only [rowCheck, rationalRow171, gridRow171, zipCheck, vertex_check223, vertex_check219, vertex_check141, vertex_check145, Bool.true_and]

theorem row_check172 : rowCheck rationalRow172 gridRow172 = true := by
  simp only [rowCheck, rationalRow172, gridRow172, zipCheck, vertex_check146, vertex_check225, vertex_check224, vertex_check223, vertex_check145, Bool.true_and]

theorem row_check173 : rowCheck rationalRow173 gridRow173 = true := by
  simp only [rowCheck, rationalRow173, gridRow173, zipCheck, vertex_check226, vertex_check227, vertex_check228, Bool.true_and]

theorem row_check174 : rowCheck rationalRow174 gridRow174 = true := by
  simp only [rowCheck, rationalRow174, gridRow174, zipCheck, vertex_check229, vertex_check230, vertex_check195, vertex_check194, vertex_check221, vertex_check220, Bool.true_and]

theorem row_check175 : rowCheck rationalRow175 gridRow175 = true := by
  simp only [rowCheck, rationalRow175, gridRow175, zipCheck, vertex_check231, vertex_check226, vertex_check228, vertex_check232, vertex_check229, vertex_check220, vertex_check224, Bool.true_and]

theorem aligned_chunk10 : ArrayAligned Row recordedOverlayVerticesChunk10 gridChunk10 := by
  have heq : recordedOverlayVerticesChunk10 = rationalChunk10 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow160, rationalRow161, rationalRow162, rationalRow163, rationalRow164, rationalRow165, rationalRow166, rationalRow167, rationalRow168, rationalRow169, rationalRow170, rationalRow171, rationalRow172, rationalRow173, rationalRow174, rationalRow175] [gridRow160, gridRow161, gridRow162, gridRow163, gridRow164, gridRow165, gridRow166, gridRow167, gridRow168, gridRow169, gridRow170, gridRow171, gridRow172, gridRow173, gridRow174, gridRow175]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow160 gridRow160 row_check160) (List.Forall₂.cons (rowCheck_sound rationalRow161 gridRow161 row_check161) (List.Forall₂.cons (rowCheck_sound rationalRow162 gridRow162 row_check162) (List.Forall₂.cons (rowCheck_sound rationalRow163 gridRow163 row_check163) (List.Forall₂.cons (rowCheck_sound rationalRow164 gridRow164 row_check164) (List.Forall₂.cons (rowCheck_sound rationalRow165 gridRow165 row_check165) (List.Forall₂.cons (rowCheck_sound rationalRow166 gridRow166 row_check166) (List.Forall₂.cons (rowCheck_sound rationalRow167 gridRow167 row_check167) (List.Forall₂.cons (rowCheck_sound rationalRow168 gridRow168 row_check168) (List.Forall₂.cons (rowCheck_sound rationalRow169 gridRow169 row_check169) (List.Forall₂.cons (rowCheck_sound rationalRow170 gridRow170 row_check170) (List.Forall₂.cons (rowCheck_sound rationalRow171 gridRow171 row_check171) (List.Forall₂.cons (rowCheck_sound rationalRow172 gridRow172 row_check172) (List.Forall₂.cons (rowCheck_sound rationalRow173 gridRow173 row_check173) (List.Forall₂.cons (rowCheck_sound rationalRow174 gridRow174 row_check174) (List.Forall₂.cons (rowCheck_sound rationalRow175 gridRow175 row_check175) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk10
