import ElevenSquare.Tasks.T04.ReverseSupport
import ElevenSquare.Pending.S07_OverlayReverseRow96
import ElevenSquare.Pending.S07_OverlayReverseRow97
import ElevenSquare.Pending.S07_OverlayReverseRow98
import ElevenSquare.Pending.S07_OverlayReverseRow99
import ElevenSquare.Pending.S07_OverlayReverseRow100
import ElevenSquare.Pending.S07_OverlayReverseRow101
import ElevenSquare.Pending.S07_OverlayReverseRow102
import ElevenSquare.Pending.S07_OverlayReverseRow103
import ElevenSquare.Pending.S07_OverlayReverseRow104
import ElevenSquare.Pending.S07_OverlayReverseRow105
import ElevenSquare.Pending.S07_OverlayReverseRow106
import ElevenSquare.Pending.S07_OverlayReverseRow107
import ElevenSquare.Pending.S07_OverlayReverseRow108
import ElevenSquare.Pending.S07_OverlayReverseRow109
import ElevenSquare.Pending.S07_OverlayReverseRow110
import ElevenSquare.Pending.S07_OverlayReverseRow111
import ElevenSquare.Pending.S07_OverlayReverseRow112
import ElevenSquare.Pending.S07_OverlayReverseRow113
import ElevenSquare.Pending.S07_OverlayReverseRow114
import ElevenSquare.Pending.S07_OverlayReverseRow115
import ElevenSquare.Pending.S07_OverlayReverseRow116
import ElevenSquare.Pending.S07_OverlayReverseRow117
import ElevenSquare.Pending.S07_OverlayReverseRow118
import ElevenSquare.Pending.S07_OverlayReverseRow119
import ElevenSquare.Pending.S07_OverlayReverseRow120
import ElevenSquare.Pending.S07_OverlayReverseRow121
import ElevenSquare.Pending.S07_OverlayReverseRow122
import ElevenSquare.Pending.S07_OverlayReverseRow123
import ElevenSquare.Pending.S07_OverlayReverseRow124
import ElevenSquare.Pending.S07_OverlayReverseRow125
import ElevenSquare.Pending.S07_OverlayReverseRow126
import ElevenSquare.Pending.S07_OverlayReverseRow127
namespace ElevenSquare.Pending.T04Reverse
open OverlayVertexChecks
open GridDistance
theorem reverse_aligned3 : ArrayAligned ReverseRowFits
    (recordedOverlayVerticesChunk6 ++ recordedOverlayVerticesChunk7) recordedOverlayLabelsChunk3 := by
  have hv : recordedOverlayVerticesChunk6 ++ recordedOverlayVerticesChunk7 = rationalChunk6 ++ rationalChunk7 := rfl
  rw [hv]
  change List.Forall₂ ReverseRowFits [rationalRow96, rationalRow97, rationalRow98, rationalRow99, rationalRow100, rationalRow101, rationalRow102, rationalRow103, rationalRow104, rationalRow105, rationalRow106, rationalRow107, rationalRow108, rationalRow109, rationalRow110, rationalRow111, rationalRow112, rationalRow113, rationalRow114, rationalRow115, rationalRow116, rationalRow117, rationalRow118, rationalRow119, rationalRow120, rationalRow121, rationalRow122, rationalRow123, rationalRow124, rationalRow125, rationalRow126, rationalRow127] [![7,0,14,12], ![7,0,14,13], ![7,0,15,8], ![7,0,15,12], ![7,0,15,13], ![7,4,10,13], ![7,4,14,12], ![7,4,14,13], ![7,4,14,14], ![7,4,15,13], ![7,5,10,8], ![7,5,10,12], ![7,5,10,13], ![7,5,15,8], ![8,10,0,7], ![8,10,5,2], ![8,10,5,3], ![8,10,5,7], ![8,11,0,2], ![8,11,1,1], ![8,11,1,2], ![8,11,1,3], ![8,11,5,2], ![8,15,0,2], ![8,15,0,3], ![8,15,0,7], ![8,15,1,2], ![8,15,1,3], ![8,15,5,2], ![8,15,5,3], ![8,15,5,7], ![9,6,2,5]]
  exact (List.Forall₂.cons overlay_in_hull96 (List.Forall₂.cons overlay_in_hull97 (List.Forall₂.cons overlay_in_hull98 (List.Forall₂.cons overlay_in_hull99 (List.Forall₂.cons overlay_in_hull100 (List.Forall₂.cons overlay_in_hull101 (List.Forall₂.cons overlay_in_hull102 (List.Forall₂.cons overlay_in_hull103 (List.Forall₂.cons overlay_in_hull104 (List.Forall₂.cons overlay_in_hull105 (List.Forall₂.cons overlay_in_hull106 (List.Forall₂.cons overlay_in_hull107 (List.Forall₂.cons overlay_in_hull108 (List.Forall₂.cons overlay_in_hull109 (List.Forall₂.cons overlay_in_hull110 (List.Forall₂.cons overlay_in_hull111 (List.Forall₂.cons overlay_in_hull112 (List.Forall₂.cons overlay_in_hull113 (List.Forall₂.cons overlay_in_hull114 (List.Forall₂.cons overlay_in_hull115 (List.Forall₂.cons overlay_in_hull116 (List.Forall₂.cons overlay_in_hull117 (List.Forall₂.cons overlay_in_hull118 (List.Forall₂.cons overlay_in_hull119 (List.Forall₂.cons overlay_in_hull120 (List.Forall₂.cons overlay_in_hull121 (List.Forall₂.cons overlay_in_hull122 (List.Forall₂.cons overlay_in_hull123 (List.Forall₂.cons overlay_in_hull124 (List.Forall₂.cons overlay_in_hull125 (List.Forall₂.cons overlay_in_hull126 (List.Forall₂.cons overlay_in_hull127 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.reverse_aligned3
