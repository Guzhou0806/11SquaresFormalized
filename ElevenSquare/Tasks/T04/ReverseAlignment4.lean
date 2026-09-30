import ElevenSquare.Tasks.T04.ReverseSupport
import ElevenSquare.Pending.S07_OverlayReverseRow128
import ElevenSquare.Pending.S07_OverlayReverseRow129
import ElevenSquare.Pending.S07_OverlayReverseRow130
import ElevenSquare.Pending.S07_OverlayReverseRow131
import ElevenSquare.Pending.S07_OverlayReverseRow132
import ElevenSquare.Pending.S07_OverlayReverseRow133
import ElevenSquare.Pending.S07_OverlayReverseRow134
import ElevenSquare.Pending.S07_OverlayReverseRow135
import ElevenSquare.Pending.S07_OverlayReverseRow136
import ElevenSquare.Pending.S07_OverlayReverseRow137
import ElevenSquare.Pending.S07_OverlayReverseRow138
import ElevenSquare.Pending.S07_OverlayReverseRow139
import ElevenSquare.Pending.S07_OverlayReverseRow140
import ElevenSquare.Pending.S07_OverlayReverseRow141
import ElevenSquare.Pending.S07_OverlayReverseRow142
import ElevenSquare.Pending.S07_OverlayReverseRow143
import ElevenSquare.Pending.S07_OverlayReverseRow144
import ElevenSquare.Pending.S07_OverlayReverseRow145
import ElevenSquare.Pending.S07_OverlayReverseRow146
import ElevenSquare.Pending.S07_OverlayReverseRow147
import ElevenSquare.Pending.S07_OverlayReverseRow148
import ElevenSquare.Pending.S07_OverlayReverseRow149
import ElevenSquare.Pending.S07_OverlayReverseRow150
import ElevenSquare.Pending.S07_OverlayReverseRow151
import ElevenSquare.Pending.S07_OverlayReverseRow152
import ElevenSquare.Pending.S07_OverlayReverseRow153
import ElevenSquare.Pending.S07_OverlayReverseRow154
import ElevenSquare.Pending.S07_OverlayReverseRow155
import ElevenSquare.Pending.S07_OverlayReverseRow156
import ElevenSquare.Pending.S07_OverlayReverseRow157
import ElevenSquare.Pending.S07_OverlayReverseRow158
import ElevenSquare.Pending.S07_OverlayReverseRow159
namespace ElevenSquare.Pending.T04Reverse
open OverlayVertexChecks
open GridDistance
theorem reverse_aligned4 : ArrayAligned ReverseRowFits
    (recordedOverlayVerticesChunk8 ++ recordedOverlayVerticesChunk9) recordedOverlayLabelsChunk4 := by
  have hv : recordedOverlayVerticesChunk8 ++ recordedOverlayVerticesChunk9 = rationalChunk8 ++ rationalChunk9 := rfl
  rw [hv]
  change List.Forall₂ ReverseRowFits [rationalRow128, rationalRow129, rationalRow130, rationalRow131, rationalRow132, rationalRow133, rationalRow134, rationalRow135, rationalRow136, rationalRow137, rationalRow138, rationalRow139, rationalRow140, rationalRow141, rationalRow142, rationalRow143, rationalRow144, rationalRow145, rationalRow146, rationalRow147, rationalRow148, rationalRow149, rationalRow150, rationalRow151, rationalRow152, rationalRow153, rationalRow154, rationalRow155, rationalRow156, rationalRow157, rationalRow158, rationalRow159] [![9,6,5,2], ![9,6,5,5], ![9,6,5,6], ![9,6,6,5], ![9,6,6,6], ![9,6,6,9], ![9,6,9,6], ![9,6,9,9], ![9,9,6,6], ![9,9,6,9], ![9,9,9,6], ![9,9,9,9], ![9,10,5,2], ![9,10,5,6], ![9,10,9,6], ![9,11,5,2], ![9,11,5,5], ![10,8,8,10], ![10,8,8,15], ![10,8,12,10], ![10,8,13,10], ![10,9,9,6], ![10,9,9,10], ![10,9,13,10], ![10,10,4,6], ![10,10,4,11], ![10,10,9,6], ![10,10,9,11], ![10,12,8,10], ![10,12,8,15], ![10,13,4,11], ![10,13,8,10]]
  exact (List.Forall₂.cons overlay_in_hull128 (List.Forall₂.cons overlay_in_hull129 (List.Forall₂.cons overlay_in_hull130 (List.Forall₂.cons overlay_in_hull131 (List.Forall₂.cons overlay_in_hull132 (List.Forall₂.cons overlay_in_hull133 (List.Forall₂.cons overlay_in_hull134 (List.Forall₂.cons overlay_in_hull135 (List.Forall₂.cons overlay_in_hull136 (List.Forall₂.cons overlay_in_hull137 (List.Forall₂.cons overlay_in_hull138 (List.Forall₂.cons overlay_in_hull139 (List.Forall₂.cons overlay_in_hull140 (List.Forall₂.cons overlay_in_hull141 (List.Forall₂.cons overlay_in_hull142 (List.Forall₂.cons overlay_in_hull143 (List.Forall₂.cons overlay_in_hull144 (List.Forall₂.cons overlay_in_hull145 (List.Forall₂.cons overlay_in_hull146 (List.Forall₂.cons overlay_in_hull147 (List.Forall₂.cons overlay_in_hull148 (List.Forall₂.cons overlay_in_hull149 (List.Forall₂.cons overlay_in_hull150 (List.Forall₂.cons overlay_in_hull151 (List.Forall₂.cons overlay_in_hull152 (List.Forall₂.cons overlay_in_hull153 (List.Forall₂.cons overlay_in_hull154 (List.Forall₂.cons overlay_in_hull155 (List.Forall₂.cons overlay_in_hull156 (List.Forall₂.cons overlay_in_hull157 (List.Forall₂.cons overlay_in_hull158 (List.Forall₂.cons overlay_in_hull159 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.reverse_aligned4
