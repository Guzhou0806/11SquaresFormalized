import ElevenSquare.Tasks.T04.ReverseSupport
import ElevenSquare.Pending.S07_OverlayReverseRow0
import ElevenSquare.Pending.S07_OverlayReverseRow1
import ElevenSquare.Pending.S07_OverlayReverseRow2
import ElevenSquare.Pending.S07_OverlayReverseRow3
import ElevenSquare.Pending.S07_OverlayReverseRow4
import ElevenSquare.Pending.S07_OverlayReverseRow5
import ElevenSquare.Pending.S07_OverlayReverseRow6
import ElevenSquare.Pending.S07_OverlayReverseRow7
import ElevenSquare.Pending.S07_OverlayReverseRow8
import ElevenSquare.Pending.S07_OverlayReverseRow9
import ElevenSquare.Pending.S07_OverlayReverseRow10
import ElevenSquare.Pending.S07_OverlayReverseRow11
import ElevenSquare.Pending.S07_OverlayReverseRow12
import ElevenSquare.Pending.S07_OverlayReverseRow13
import ElevenSquare.Pending.S07_OverlayReverseRow14
import ElevenSquare.Pending.S07_OverlayReverseRow15
import ElevenSquare.Pending.S07_OverlayReverseRow16
import ElevenSquare.Pending.S07_OverlayReverseRow17
import ElevenSquare.Pending.S07_OverlayReverseRow18
import ElevenSquare.Pending.S07_OverlayReverseRow19
import ElevenSquare.Pending.S07_OverlayReverseRow20
import ElevenSquare.Pending.S07_OverlayReverseRow21
import ElevenSquare.Pending.S07_OverlayReverseRow22
import ElevenSquare.Pending.S07_OverlayReverseRow23
import ElevenSquare.Pending.S07_OverlayReverseRow24
import ElevenSquare.Pending.S07_OverlayReverseRow25
import ElevenSquare.Pending.S07_OverlayReverseRow26
import ElevenSquare.Pending.S07_OverlayReverseRow27
import ElevenSquare.Pending.S07_OverlayReverseRow28
import ElevenSquare.Pending.S07_OverlayReverseRow29
import ElevenSquare.Pending.S07_OverlayReverseRow30
import ElevenSquare.Pending.S07_OverlayReverseRow31
namespace ElevenSquare.Pending.T04Reverse
open OverlayVertexChecks
open GridDistance
theorem reverse_aligned0 : ArrayAligned ReverseRowFits
    (recordedOverlayVerticesChunk0 ++ recordedOverlayVerticesChunk1) recordedOverlayLabelsChunk0 := by
  have hv : recordedOverlayVerticesChunk0 ++ recordedOverlayVerticesChunk1 = rationalChunk0 ++ rationalChunk1 := rfl
  rw [hv]
  change List.Forall₂ ReverseRowFits [rationalRow0, rationalRow1, rationalRow2, rationalRow3, rationalRow4, rationalRow5, rationalRow6, rationalRow7, rationalRow8, rationalRow9, rationalRow10, rationalRow11, rationalRow12, rationalRow13, rationalRow14, rationalRow15, rationalRow16, rationalRow17, rationalRow18, rationalRow19, rationalRow20, rationalRow21, rationalRow22, rationalRow23, rationalRow24, rationalRow25, rationalRow26, rationalRow27, rationalRow28, rationalRow29, rationalRow30, rationalRow31] [![0,2,7,0], ![0,2,7,4], ![0,3,3,0], ![0,3,7,0], ![0,7,2,0], ![0,7,2,1], ![0,7,2,5], ![0,7,3,0], ![0,7,3,1], ![0,7,3,5], ![0,7,7,0], ![0,7,7,5], ![1,1,7,4], ![1,1,11,4], ![1,1,11,8], ![1,2,7,0], ![1,2,7,4], ![1,2,11,4], ![1,3,7,0], ![1,3,7,4], ![2,0,11,8], ![2,0,15,8], ![2,1,11,4], ![2,1,11,8], ![2,1,15,8], ![2,2,11,4], ![2,5,6,9], ![2,5,10,8], ![2,5,10,9], ![2,5,10,13], ![2,5,11,4], ![2,5,11,8]]
  exact (List.Forall₂.cons overlay_in_hull0 (List.Forall₂.cons overlay_in_hull1 (List.Forall₂.cons overlay_in_hull2 (List.Forall₂.cons overlay_in_hull3 (List.Forall₂.cons overlay_in_hull4 (List.Forall₂.cons overlay_in_hull5 (List.Forall₂.cons overlay_in_hull6 (List.Forall₂.cons overlay_in_hull7 (List.Forall₂.cons overlay_in_hull8 (List.Forall₂.cons overlay_in_hull9 (List.Forall₂.cons overlay_in_hull10 (List.Forall₂.cons overlay_in_hull11 (List.Forall₂.cons overlay_in_hull12 (List.Forall₂.cons overlay_in_hull13 (List.Forall₂.cons overlay_in_hull14 (List.Forall₂.cons overlay_in_hull15 (List.Forall₂.cons overlay_in_hull16 (List.Forall₂.cons overlay_in_hull17 (List.Forall₂.cons overlay_in_hull18 (List.Forall₂.cons overlay_in_hull19 (List.Forall₂.cons overlay_in_hull20 (List.Forall₂.cons overlay_in_hull21 (List.Forall₂.cons overlay_in_hull22 (List.Forall₂.cons overlay_in_hull23 (List.Forall₂.cons overlay_in_hull24 (List.Forall₂.cons overlay_in_hull25 (List.Forall₂.cons overlay_in_hull26 (List.Forall₂.cons overlay_in_hull27 (List.Forall₂.cons overlay_in_hull28 (List.Forall₂.cons overlay_in_hull29 (List.Forall₂.cons overlay_in_hull30 (List.Forall₂.cons overlay_in_hull31 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.reverse_aligned0
