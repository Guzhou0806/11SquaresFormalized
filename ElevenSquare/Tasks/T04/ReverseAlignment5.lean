import ElevenSquare.Tasks.T04.ReverseSupport
import ElevenSquare.Pending.S07_OverlayReverseRow160
import ElevenSquare.Pending.S07_OverlayReverseRow161
import ElevenSquare.Pending.S07_OverlayReverseRow162
import ElevenSquare.Pending.S07_OverlayReverseRow163
import ElevenSquare.Pending.S07_OverlayReverseRow164
import ElevenSquare.Pending.S07_OverlayReverseRow165
import ElevenSquare.Pending.S07_OverlayReverseRow166
import ElevenSquare.Pending.S07_OverlayReverseRow167
import ElevenSquare.Pending.S07_OverlayReverseRow168
import ElevenSquare.Pending.S07_OverlayReverseRow169
import ElevenSquare.Pending.S07_OverlayReverseRow170
import ElevenSquare.Pending.S07_OverlayReverseRow171
import ElevenSquare.Pending.S07_OverlayReverseRow172
import ElevenSquare.Pending.S07_OverlayReverseRow173
import ElevenSquare.Pending.S07_OverlayReverseRow174
import ElevenSquare.Pending.S07_OverlayReverseRow175
import ElevenSquare.Pending.S07_OverlayReverseRow176
import ElevenSquare.Pending.S07_OverlayReverseRow177
import ElevenSquare.Pending.S07_OverlayReverseRow178
import ElevenSquare.Pending.S07_OverlayReverseRow179
import ElevenSquare.Pending.S07_OverlayReverseRow180
import ElevenSquare.Pending.S07_OverlayReverseRow181
import ElevenSquare.Pending.S07_OverlayReverseRow182
import ElevenSquare.Pending.S07_OverlayReverseRow183
import ElevenSquare.Pending.S07_OverlayReverseRow184
import ElevenSquare.Pending.S07_OverlayReverseRow185
import ElevenSquare.Pending.S07_OverlayReverseRow186
import ElevenSquare.Pending.S07_OverlayReverseRow187
import ElevenSquare.Pending.S07_OverlayReverseRow188
import ElevenSquare.Pending.S07_OverlayReverseRow189
import ElevenSquare.Pending.S07_OverlayReverseRow190
import ElevenSquare.Pending.S07_OverlayReverseRow191
namespace ElevenSquare.Pending.T04Reverse
open OverlayVertexChecks
open GridDistance
theorem reverse_aligned5 : ArrayAligned ReverseRowFits
    (recordedOverlayVerticesChunk10 ++ recordedOverlayVerticesChunk11) recordedOverlayLabelsChunk5 := by
  have hv : recordedOverlayVerticesChunk10 ++ recordedOverlayVerticesChunk11 = rationalChunk10 ++ rationalChunk11 := rfl
  rw [hv]
  change List.Forall₂ ReverseRowFits [rationalRow160, rationalRow161, rationalRow162, rationalRow163, rationalRow164, rationalRow165, rationalRow166, rationalRow167, rationalRow168, rationalRow169, rationalRow170, rationalRow171, rationalRow172, rationalRow173, rationalRow174, rationalRow175, rationalRow176, rationalRow177, rationalRow178, rationalRow179, rationalRow180, rationalRow181, rationalRow182, rationalRow183, rationalRow184, rationalRow185, rationalRow186, rationalRow187, rationalRow188, rationalRow189, rationalRow190, rationalRow191] [![10,13,8,11], ![10,13,8,15], ![10,13,9,6], ![10,13,9,10], ![10,13,9,11], ![10,13,13,10], ![11,4,10,10], ![11,4,10,13], ![11,4,13,10], ![11,4,13,13], ![11,4,13,14], ![11,4,14,13], ![11,4,14,14], ![11,8,12,14], ![11,8,13,10], ![11,8,13,14], ![11,8,13,15], ![11,8,14,14], ![11,9,10,10], ![11,9,13,10], ![12,10,0,7], ![12,10,5,7], ![12,14,0,7], ![12,14,4,7], ![12,15,0,3], ![12,15,0,7], ![13,10,0,7], ![13,10,4,6], ![13,10,4,7], ![13,10,4,11], ![13,10,5,2], ![13,10,5,6]]
  exact (List.Forall₂.cons overlay_in_hull160 (List.Forall₂.cons overlay_in_hull161 (List.Forall₂.cons overlay_in_hull162 (List.Forall₂.cons overlay_in_hull163 (List.Forall₂.cons overlay_in_hull164 (List.Forall₂.cons overlay_in_hull165 (List.Forall₂.cons overlay_in_hull166 (List.Forall₂.cons overlay_in_hull167 (List.Forall₂.cons overlay_in_hull168 (List.Forall₂.cons overlay_in_hull169 (List.Forall₂.cons overlay_in_hull170 (List.Forall₂.cons overlay_in_hull171 (List.Forall₂.cons overlay_in_hull172 (List.Forall₂.cons overlay_in_hull173 (List.Forall₂.cons overlay_in_hull174 (List.Forall₂.cons overlay_in_hull175 (List.Forall₂.cons overlay_in_hull176 (List.Forall₂.cons overlay_in_hull177 (List.Forall₂.cons overlay_in_hull178 (List.Forall₂.cons overlay_in_hull179 (List.Forall₂.cons overlay_in_hull180 (List.Forall₂.cons overlay_in_hull181 (List.Forall₂.cons overlay_in_hull182 (List.Forall₂.cons overlay_in_hull183 (List.Forall₂.cons overlay_in_hull184 (List.Forall₂.cons overlay_in_hull185 (List.Forall₂.cons overlay_in_hull186 (List.Forall₂.cons overlay_in_hull187 (List.Forall₂.cons overlay_in_hull188 (List.Forall₂.cons overlay_in_hull189 (List.Forall₂.cons overlay_in_hull190 (List.Forall₂.cons overlay_in_hull191 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.reverse_aligned5
