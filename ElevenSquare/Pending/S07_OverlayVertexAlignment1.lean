import ElevenSquare.Pending.S07_OverlayVertexSupport
import ElevenSquare.Pending.S07_OverlayVertexChecks4
import ElevenSquare.Pending.S07_OverlayVertexChecks5
import ElevenSquare.Pending.S07_OverlayVertexChecks6
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem vertices_aligned1 : ArrayAligned VertexRowFits
    (recordedOverlayVerticesChunk2 ++ recordedOverlayVerticesChunk3) recordedOverlayLabelsChunk1 := by
  have hv : recordedOverlayVerticesChunk2 ++ recordedOverlayVerticesChunk3 = rationalChunk2 ++ rationalChunk3 := rfl
  rw [hv]
  change List.Forall₂ VertexRowFits [rationalRow32, rationalRow33, rationalRow34, rationalRow35, rationalRow36, rationalRow37, rationalRow38, rationalRow39, rationalRow40, rationalRow41, rationalRow42, rationalRow43, rationalRow44, rationalRow45, rationalRow46, rationalRow47, rationalRow48, rationalRow49, rationalRow50, rationalRow51, rationalRow52, rationalRow53, rationalRow54, rationalRow55, rationalRow56, rationalRow57, rationalRow58, rationalRow59, rationalRow60, rationalRow61, rationalRow62, rationalRow63] [![2,5,11,9], ![2,5,15,8], ![3,0,15,8], ![3,0,15,12], ![3,1,11,8], ![3,1,15,8], ![3,5,10,8], ![3,5,15,8], ![4,6,2,5], ![4,6,5,5], ![4,7,1,1], ![4,7,2,0], ![4,7,2,1], ![4,7,2,5], ![4,7,3,1], ![4,11,1,1], ![4,11,1,2], ![4,11,2,1], ![4,11,2,2], ![4,11,2,5], ![4,11,5,2], ![4,11,5,5], ![5,2,2,5], ![5,2,6,4], ![5,2,6,5], ![5,2,6,9], ![5,2,7,0], ![5,2,7,4], ![5,2,7,5], ![5,2,11,4], ![5,3,7,0], ![5,3,7,5]]
  exact (List.Forall₂.cons vertices_fit32 (List.Forall₂.cons vertices_fit33 (List.Forall₂.cons vertices_fit34 (List.Forall₂.cons vertices_fit35 (List.Forall₂.cons vertices_fit36 (List.Forall₂.cons vertices_fit37 (List.Forall₂.cons vertices_fit38 (List.Forall₂.cons vertices_fit39 (List.Forall₂.cons vertices_fit40 (List.Forall₂.cons vertices_fit41 (List.Forall₂.cons vertices_fit42 (List.Forall₂.cons vertices_fit43 (List.Forall₂.cons vertices_fit44 (List.Forall₂.cons vertices_fit45 (List.Forall₂.cons vertices_fit46 (List.Forall₂.cons vertices_fit47 (List.Forall₂.cons vertices_fit48 (List.Forall₂.cons vertices_fit49 (List.Forall₂.cons vertices_fit50 (List.Forall₂.cons vertices_fit51 (List.Forall₂.cons vertices_fit52 (List.Forall₂.cons vertices_fit53 (List.Forall₂.cons vertices_fit54 (List.Forall₂.cons vertices_fit55 (List.Forall₂.cons vertices_fit56 (List.Forall₂.cons vertices_fit57 (List.Forall₂.cons vertices_fit58 (List.Forall₂.cons vertices_fit59 (List.Forall₂.cons vertices_fit60 (List.Forall₂.cons vertices_fit61 (List.Forall₂.cons vertices_fit62 (List.Forall₂.cons vertices_fit63 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_aligned1
