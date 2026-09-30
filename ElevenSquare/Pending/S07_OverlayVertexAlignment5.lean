import ElevenSquare.Pending.S07_OverlayVertexSupport
import ElevenSquare.Pending.S07_OverlayVertexChecks20
import ElevenSquare.Pending.S07_OverlayVertexChecks21
import ElevenSquare.Pending.S07_OverlayVertexChecks22
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem vertices_aligned5 : ArrayAligned VertexRowFits
    (recordedOverlayVerticesChunk10 ++ recordedOverlayVerticesChunk11) recordedOverlayLabelsChunk5 := by
  have hv : recordedOverlayVerticesChunk10 ++ recordedOverlayVerticesChunk11 = rationalChunk10 ++ rationalChunk11 := rfl
  rw [hv]
  change List.Forall₂ VertexRowFits [rationalRow160, rationalRow161, rationalRow162, rationalRow163, rationalRow164, rationalRow165, rationalRow166, rationalRow167, rationalRow168, rationalRow169, rationalRow170, rationalRow171, rationalRow172, rationalRow173, rationalRow174, rationalRow175, rationalRow176, rationalRow177, rationalRow178, rationalRow179, rationalRow180, rationalRow181, rationalRow182, rationalRow183, rationalRow184, rationalRow185, rationalRow186, rationalRow187, rationalRow188, rationalRow189, rationalRow190, rationalRow191] [![10,13,8,11], ![10,13,8,15], ![10,13,9,6], ![10,13,9,10], ![10,13,9,11], ![10,13,13,10], ![11,4,10,10], ![11,4,10,13], ![11,4,13,10], ![11,4,13,13], ![11,4,13,14], ![11,4,14,13], ![11,4,14,14], ![11,8,12,14], ![11,8,13,10], ![11,8,13,14], ![11,8,13,15], ![11,8,14,14], ![11,9,10,10], ![11,9,13,10], ![12,10,0,7], ![12,10,5,7], ![12,14,0,7], ![12,14,4,7], ![12,15,0,3], ![12,15,0,7], ![13,10,0,7], ![13,10,4,6], ![13,10,4,7], ![13,10,4,11], ![13,10,5,2], ![13,10,5,6]]
  exact (List.Forall₂.cons vertices_fit160 (List.Forall₂.cons vertices_fit161 (List.Forall₂.cons vertices_fit162 (List.Forall₂.cons vertices_fit163 (List.Forall₂.cons vertices_fit164 (List.Forall₂.cons vertices_fit165 (List.Forall₂.cons vertices_fit166 (List.Forall₂.cons vertices_fit167 (List.Forall₂.cons vertices_fit168 (List.Forall₂.cons vertices_fit169 (List.Forall₂.cons vertices_fit170 (List.Forall₂.cons vertices_fit171 (List.Forall₂.cons vertices_fit172 (List.Forall₂.cons vertices_fit173 (List.Forall₂.cons vertices_fit174 (List.Forall₂.cons vertices_fit175 (List.Forall₂.cons vertices_fit176 (List.Forall₂.cons vertices_fit177 (List.Forall₂.cons vertices_fit178 (List.Forall₂.cons vertices_fit179 (List.Forall₂.cons vertices_fit180 (List.Forall₂.cons vertices_fit181 (List.Forall₂.cons vertices_fit182 (List.Forall₂.cons vertices_fit183 (List.Forall₂.cons vertices_fit184 (List.Forall₂.cons vertices_fit185 (List.Forall₂.cons vertices_fit186 (List.Forall₂.cons vertices_fit187 (List.Forall₂.cons vertices_fit188 (List.Forall₂.cons vertices_fit189 (List.Forall₂.cons vertices_fit190 (List.Forall₂.cons vertices_fit191 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_aligned5
