import ElevenSquare.Pending.S07_OverlayVertexSupport
import ElevenSquare.Pending.S07_OverlayVertexChecks8
import ElevenSquare.Pending.S07_OverlayVertexChecks9
import ElevenSquare.Pending.S07_OverlayVertexChecks10
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem vertices_aligned2 : ArrayAligned VertexRowFits
    (recordedOverlayVerticesChunk4 ++ recordedOverlayVerticesChunk5) recordedOverlayLabelsChunk2 := by
  have hv : recordedOverlayVerticesChunk4 ++ recordedOverlayVerticesChunk5 = rationalChunk4 ++ rationalChunk5 := rfl
  rw [hv]
  change List.Forall₂ VertexRowFits [rationalRow64, rationalRow65, rationalRow66, rationalRow67, rationalRow68, rationalRow69, rationalRow70, rationalRow71, rationalRow72, rationalRow73, rationalRow74, rationalRow75, rationalRow76, rationalRow77, rationalRow78, rationalRow79, rationalRow80, rationalRow81, rationalRow82, rationalRow83, rationalRow84, rationalRow85, rationalRow86, rationalRow87, rationalRow88, rationalRow89, rationalRow90, rationalRow91, rationalRow92, rationalRow93, rationalRow94, rationalRow95] [![5,5,6,4], ![5,5,6,9], ![5,5,11,4], ![5,5,11,9], ![5,6,2,5], ![5,6,6,5], ![5,6,6,9], ![5,7,2,5], ![5,7,3,5], ![5,7,7,0], ![5,7,7,5], ![6,4,10,10], ![6,4,10,13], ![6,5,6,9], ![6,5,10,9], ![6,5,10,13], ![6,6,6,6], ![6,6,6,9], ![6,6,9,6], ![6,6,9,9], ![6,9,6,6], ![6,9,6,9], ![6,9,9,6], ![6,9,9,9], ![6,9,9,10], ![6,9,10,9], ![6,9,10,10], ![6,9,10,13], ![6,9,13,10], ![7,0,10,8], ![7,0,10,12], ![7,0,10,13]]
  exact (List.Forall₂.cons vertices_fit64 (List.Forall₂.cons vertices_fit65 (List.Forall₂.cons vertices_fit66 (List.Forall₂.cons vertices_fit67 (List.Forall₂.cons vertices_fit68 (List.Forall₂.cons vertices_fit69 (List.Forall₂.cons vertices_fit70 (List.Forall₂.cons vertices_fit71 (List.Forall₂.cons vertices_fit72 (List.Forall₂.cons vertices_fit73 (List.Forall₂.cons vertices_fit74 (List.Forall₂.cons vertices_fit75 (List.Forall₂.cons vertices_fit76 (List.Forall₂.cons vertices_fit77 (List.Forall₂.cons vertices_fit78 (List.Forall₂.cons vertices_fit79 (List.Forall₂.cons vertices_fit80 (List.Forall₂.cons vertices_fit81 (List.Forall₂.cons vertices_fit82 (List.Forall₂.cons vertices_fit83 (List.Forall₂.cons vertices_fit84 (List.Forall₂.cons vertices_fit85 (List.Forall₂.cons vertices_fit86 (List.Forall₂.cons vertices_fit87 (List.Forall₂.cons vertices_fit88 (List.Forall₂.cons vertices_fit89 (List.Forall₂.cons vertices_fit90 (List.Forall₂.cons vertices_fit91 (List.Forall₂.cons vertices_fit92 (List.Forall₂.cons vertices_fit93 (List.Forall₂.cons vertices_fit94 (List.Forall₂.cons vertices_fit95 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_aligned2
