import ElevenSquare.Tasks.T04.ReverseSupport
import ElevenSquare.Pending.S07_OverlayReverseRow32
import ElevenSquare.Pending.S07_OverlayReverseRow33
import ElevenSquare.Pending.S07_OverlayReverseRow34
import ElevenSquare.Pending.S07_OverlayReverseRow35
import ElevenSquare.Pending.S07_OverlayReverseRow36
import ElevenSquare.Pending.S07_OverlayReverseRow37
import ElevenSquare.Pending.S07_OverlayReverseRow38
import ElevenSquare.Pending.S07_OverlayReverseRow39
import ElevenSquare.Pending.S07_OverlayReverseRow40
import ElevenSquare.Pending.S07_OverlayReverseRow41
import ElevenSquare.Pending.S07_OverlayReverseRow42
import ElevenSquare.Pending.S07_OverlayReverseRow43
import ElevenSquare.Pending.S07_OverlayReverseRow44
import ElevenSquare.Pending.S07_OverlayReverseRow45
import ElevenSquare.Pending.S07_OverlayReverseRow46
import ElevenSquare.Pending.S07_OverlayReverseRow47
import ElevenSquare.Pending.S07_OverlayReverseRow48
import ElevenSquare.Pending.S07_OverlayReverseRow49
import ElevenSquare.Pending.S07_OverlayReverseRow50
import ElevenSquare.Pending.S07_OverlayReverseRow51
import ElevenSquare.Pending.S07_OverlayReverseRow52
import ElevenSquare.Pending.S07_OverlayReverseRow53
import ElevenSquare.Pending.S07_OverlayReverseRow54
import ElevenSquare.Pending.S07_OverlayReverseRow55
import ElevenSquare.Pending.S07_OverlayReverseRow56
import ElevenSquare.Pending.S07_OverlayReverseRow57
import ElevenSquare.Pending.S07_OverlayReverseRow58
import ElevenSquare.Pending.S07_OverlayReverseRow59
import ElevenSquare.Pending.S07_OverlayReverseRow60
import ElevenSquare.Pending.S07_OverlayReverseRow61
import ElevenSquare.Pending.S07_OverlayReverseRow62
import ElevenSquare.Pending.S07_OverlayReverseRow63
namespace ElevenSquare.Pending.T04Reverse
open OverlayVertexChecks
open GridDistance
theorem reverse_aligned1 : ArrayAligned ReverseRowFits
    (recordedOverlayVerticesChunk2 ++ recordedOverlayVerticesChunk3) recordedOverlayLabelsChunk1 := by
  have hv : recordedOverlayVerticesChunk2 ++ recordedOverlayVerticesChunk3 = rationalChunk2 ++ rationalChunk3 := rfl
  rw [hv]
  change List.Forall₂ ReverseRowFits [rationalRow32, rationalRow33, rationalRow34, rationalRow35, rationalRow36, rationalRow37, rationalRow38, rationalRow39, rationalRow40, rationalRow41, rationalRow42, rationalRow43, rationalRow44, rationalRow45, rationalRow46, rationalRow47, rationalRow48, rationalRow49, rationalRow50, rationalRow51, rationalRow52, rationalRow53, rationalRow54, rationalRow55, rationalRow56, rationalRow57, rationalRow58, rationalRow59, rationalRow60, rationalRow61, rationalRow62, rationalRow63] [![2,5,11,9], ![2,5,15,8], ![3,0,15,8], ![3,0,15,12], ![3,1,11,8], ![3,1,15,8], ![3,5,10,8], ![3,5,15,8], ![4,6,2,5], ![4,6,5,5], ![4,7,1,1], ![4,7,2,0], ![4,7,2,1], ![4,7,2,5], ![4,7,3,1], ![4,11,1,1], ![4,11,1,2], ![4,11,2,1], ![4,11,2,2], ![4,11,2,5], ![4,11,5,2], ![4,11,5,5], ![5,2,2,5], ![5,2,6,4], ![5,2,6,5], ![5,2,6,9], ![5,2,7,0], ![5,2,7,4], ![5,2,7,5], ![5,2,11,4], ![5,3,7,0], ![5,3,7,5]]
  exact (List.Forall₂.cons overlay_in_hull32 (List.Forall₂.cons overlay_in_hull33 (List.Forall₂.cons overlay_in_hull34 (List.Forall₂.cons overlay_in_hull35 (List.Forall₂.cons overlay_in_hull36 (List.Forall₂.cons overlay_in_hull37 (List.Forall₂.cons overlay_in_hull38 (List.Forall₂.cons overlay_in_hull39 (List.Forall₂.cons overlay_in_hull40 (List.Forall₂.cons overlay_in_hull41 (List.Forall₂.cons overlay_in_hull42 (List.Forall₂.cons overlay_in_hull43 (List.Forall₂.cons overlay_in_hull44 (List.Forall₂.cons overlay_in_hull45 (List.Forall₂.cons overlay_in_hull46 (List.Forall₂.cons overlay_in_hull47 (List.Forall₂.cons overlay_in_hull48 (List.Forall₂.cons overlay_in_hull49 (List.Forall₂.cons overlay_in_hull50 (List.Forall₂.cons overlay_in_hull51 (List.Forall₂.cons overlay_in_hull52 (List.Forall₂.cons overlay_in_hull53 (List.Forall₂.cons overlay_in_hull54 (List.Forall₂.cons overlay_in_hull55 (List.Forall₂.cons overlay_in_hull56 (List.Forall₂.cons overlay_in_hull57 (List.Forall₂.cons overlay_in_hull58 (List.Forall₂.cons overlay_in_hull59 (List.Forall₂.cons overlay_in_hull60 (List.Forall₂.cons overlay_in_hull61 (List.Forall₂.cons overlay_in_hull62 (List.Forall₂.cons overlay_in_hull63 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.reverse_aligned1
