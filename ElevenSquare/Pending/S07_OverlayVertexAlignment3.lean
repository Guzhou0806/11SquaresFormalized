import ElevenSquare.Pending.S07_OverlayVertexSupport
import ElevenSquare.Pending.S07_OverlayVertexChecks12
import ElevenSquare.Pending.S07_OverlayVertexChecks13
import ElevenSquare.Pending.S07_OverlayVertexChecks14
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem vertices_aligned3 : ArrayAligned VertexRowFits
    (recordedOverlayVerticesChunk6 ++ recordedOverlayVerticesChunk7) recordedOverlayLabelsChunk3 := by
  have hv : recordedOverlayVerticesChunk6 ++ recordedOverlayVerticesChunk7 = rationalChunk6 ++ rationalChunk7 := rfl
  rw [hv]
  change List.Forall₂ VertexRowFits [rationalRow96, rationalRow97, rationalRow98, rationalRow99, rationalRow100, rationalRow101, rationalRow102, rationalRow103, rationalRow104, rationalRow105, rationalRow106, rationalRow107, rationalRow108, rationalRow109, rationalRow110, rationalRow111, rationalRow112, rationalRow113, rationalRow114, rationalRow115, rationalRow116, rationalRow117, rationalRow118, rationalRow119, rationalRow120, rationalRow121, rationalRow122, rationalRow123, rationalRow124, rationalRow125, rationalRow126, rationalRow127] [![7,0,14,12], ![7,0,14,13], ![7,0,15,8], ![7,0,15,12], ![7,0,15,13], ![7,4,10,13], ![7,4,14,12], ![7,4,14,13], ![7,4,14,14], ![7,4,15,13], ![7,5,10,8], ![7,5,10,12], ![7,5,10,13], ![7,5,15,8], ![8,10,0,7], ![8,10,5,2], ![8,10,5,3], ![8,10,5,7], ![8,11,0,2], ![8,11,1,1], ![8,11,1,2], ![8,11,1,3], ![8,11,5,2], ![8,15,0,2], ![8,15,0,3], ![8,15,0,7], ![8,15,1,2], ![8,15,1,3], ![8,15,5,2], ![8,15,5,3], ![8,15,5,7], ![9,6,2,5]]
  exact (List.Forall₂.cons vertices_fit96 (List.Forall₂.cons vertices_fit97 (List.Forall₂.cons vertices_fit98 (List.Forall₂.cons vertices_fit99 (List.Forall₂.cons vertices_fit100 (List.Forall₂.cons vertices_fit101 (List.Forall₂.cons vertices_fit102 (List.Forall₂.cons vertices_fit103 (List.Forall₂.cons vertices_fit104 (List.Forall₂.cons vertices_fit105 (List.Forall₂.cons vertices_fit106 (List.Forall₂.cons vertices_fit107 (List.Forall₂.cons vertices_fit108 (List.Forall₂.cons vertices_fit109 (List.Forall₂.cons vertices_fit110 (List.Forall₂.cons vertices_fit111 (List.Forall₂.cons vertices_fit112 (List.Forall₂.cons vertices_fit113 (List.Forall₂.cons vertices_fit114 (List.Forall₂.cons vertices_fit115 (List.Forall₂.cons vertices_fit116 (List.Forall₂.cons vertices_fit117 (List.Forall₂.cons vertices_fit118 (List.Forall₂.cons vertices_fit119 (List.Forall₂.cons vertices_fit120 (List.Forall₂.cons vertices_fit121 (List.Forall₂.cons vertices_fit122 (List.Forall₂.cons vertices_fit123 (List.Forall₂.cons vertices_fit124 (List.Forall₂.cons vertices_fit125 (List.Forall₂.cons vertices_fit126 (List.Forall₂.cons vertices_fit127 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_aligned3
