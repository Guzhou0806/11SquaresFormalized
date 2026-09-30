import ElevenSquare.Pending.S07_OverlayVertexSupport
import ElevenSquare.Pending.S07_OverlayVertexChecks0
import ElevenSquare.Pending.S07_OverlayVertexChecks1
import ElevenSquare.Pending.S07_OverlayVertexChecks2
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem vertices_aligned0 : ArrayAligned VertexRowFits
    (recordedOverlayVerticesChunk0 ++ recordedOverlayVerticesChunk1) recordedOverlayLabelsChunk0 := by
  have hv : recordedOverlayVerticesChunk0 ++ recordedOverlayVerticesChunk1 = rationalChunk0 ++ rationalChunk1 := rfl
  rw [hv]
  change List.Forall₂ VertexRowFits [rationalRow0, rationalRow1, rationalRow2, rationalRow3, rationalRow4, rationalRow5, rationalRow6, rationalRow7, rationalRow8, rationalRow9, rationalRow10, rationalRow11, rationalRow12, rationalRow13, rationalRow14, rationalRow15, rationalRow16, rationalRow17, rationalRow18, rationalRow19, rationalRow20, rationalRow21, rationalRow22, rationalRow23, rationalRow24, rationalRow25, rationalRow26, rationalRow27, rationalRow28, rationalRow29, rationalRow30, rationalRow31] [![0,2,7,0], ![0,2,7,4], ![0,3,3,0], ![0,3,7,0], ![0,7,2,0], ![0,7,2,1], ![0,7,2,5], ![0,7,3,0], ![0,7,3,1], ![0,7,3,5], ![0,7,7,0], ![0,7,7,5], ![1,1,7,4], ![1,1,11,4], ![1,1,11,8], ![1,2,7,0], ![1,2,7,4], ![1,2,11,4], ![1,3,7,0], ![1,3,7,4], ![2,0,11,8], ![2,0,15,8], ![2,1,11,4], ![2,1,11,8], ![2,1,15,8], ![2,2,11,4], ![2,5,6,9], ![2,5,10,8], ![2,5,10,9], ![2,5,10,13], ![2,5,11,4], ![2,5,11,8]]
  exact (List.Forall₂.cons vertices_fit0 (List.Forall₂.cons vertices_fit1 (List.Forall₂.cons vertices_fit2 (List.Forall₂.cons vertices_fit3 (List.Forall₂.cons vertices_fit4 (List.Forall₂.cons vertices_fit5 (List.Forall₂.cons vertices_fit6 (List.Forall₂.cons vertices_fit7 (List.Forall₂.cons vertices_fit8 (List.Forall₂.cons vertices_fit9 (List.Forall₂.cons vertices_fit10 (List.Forall₂.cons vertices_fit11 (List.Forall₂.cons vertices_fit12 (List.Forall₂.cons vertices_fit13 (List.Forall₂.cons vertices_fit14 (List.Forall₂.cons vertices_fit15 (List.Forall₂.cons vertices_fit16 (List.Forall₂.cons vertices_fit17 (List.Forall₂.cons vertices_fit18 (List.Forall₂.cons vertices_fit19 (List.Forall₂.cons vertices_fit20 (List.Forall₂.cons vertices_fit21 (List.Forall₂.cons vertices_fit22 (List.Forall₂.cons vertices_fit23 (List.Forall₂.cons vertices_fit24 (List.Forall₂.cons vertices_fit25 (List.Forall₂.cons vertices_fit26 (List.Forall₂.cons vertices_fit27 (List.Forall₂.cons vertices_fit28 (List.Forall₂.cons vertices_fit29 (List.Forall₂.cons vertices_fit30 (List.Forall₂.cons vertices_fit31 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_aligned0
