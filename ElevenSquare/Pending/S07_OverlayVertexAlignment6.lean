import ElevenSquare.Pending.S07_OverlayVertexSupport
import ElevenSquare.Pending.S07_OverlayVertexChecks24
import ElevenSquare.Pending.S07_OverlayVertexChecks25
import ElevenSquare.Pending.S07_OverlayVertexChecks26
import ElevenSquare.Pending.S07_OverlayVertexChecks27
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem vertices_aligned6 : ArrayAligned VertexRowFits
    (recordedOverlayVerticesChunk12 ++ recordedOverlayVerticesChunk13) recordedOverlayLabelsChunk6 := by
  have hv : recordedOverlayVerticesChunk12 ++ recordedOverlayVerticesChunk13 = rationalChunk12 ++ rationalChunk13 := rfl
  rw [hv]
  change List.Forall₂ VertexRowFits [rationalRow192, rationalRow193, rationalRow194, rationalRow195, rationalRow196, rationalRow197, rationalRow198, rationalRow199, rationalRow200, rationalRow201, rationalRow202, rationalRow203, rationalRow204, rationalRow205, rationalRow206, rationalRow207, rationalRow208, rationalRow209, rationalRow210, rationalRow211, rationalRow212, rationalRow213, rationalRow214, rationalRow215, rationalRow216, rationalRow217, rationalRow218, rationalRow219] [![13,10,5,7], ![13,10,9,6], ![13,13,4,11], ![13,14,0,7], ![13,14,4,7], ![13,14,4,11], ![13,15,0,7], ![13,15,4,7], ![14,12,8,11], ![14,12,8,15], ![14,13,4,11], ![14,13,8,11], ![14,13,8,15], ![14,14,4,7], ![14,14,4,11], ![14,14,8,11], ![15,8,8,10], ![15,8,8,15], ![15,8,12,10], ![15,8,12,14], ![15,8,12,15], ![15,8,13,10], ![15,8,13,14], ![15,8,13,15], ![15,12,8,15], ![15,12,12,15], ![15,13,8,11], ![15,13,8,15]]
  exact (List.Forall₂.cons vertices_fit192 (List.Forall₂.cons vertices_fit193 (List.Forall₂.cons vertices_fit194 (List.Forall₂.cons vertices_fit195 (List.Forall₂.cons vertices_fit196 (List.Forall₂.cons vertices_fit197 (List.Forall₂.cons vertices_fit198 (List.Forall₂.cons vertices_fit199 (List.Forall₂.cons vertices_fit200 (List.Forall₂.cons vertices_fit201 (List.Forall₂.cons vertices_fit202 (List.Forall₂.cons vertices_fit203 (List.Forall₂.cons vertices_fit204 (List.Forall₂.cons vertices_fit205 (List.Forall₂.cons vertices_fit206 (List.Forall₂.cons vertices_fit207 (List.Forall₂.cons vertices_fit208 (List.Forall₂.cons vertices_fit209 (List.Forall₂.cons vertices_fit210 (List.Forall₂.cons vertices_fit211 (List.Forall₂.cons vertices_fit212 (List.Forall₂.cons vertices_fit213 (List.Forall₂.cons vertices_fit214 (List.Forall₂.cons vertices_fit215 (List.Forall₂.cons vertices_fit216 (List.Forall₂.cons vertices_fit217 (List.Forall₂.cons vertices_fit218 (List.Forall₂.cons vertices_fit219 List.Forall₂.nil))))))))))))))))))))))))))))
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_aligned6
