import ElevenSquare.Tasks.T04.ReverseSupport
import ElevenSquare.Pending.S07_OverlayReverseRow192
import ElevenSquare.Pending.S07_OverlayReverseRow193
import ElevenSquare.Pending.S07_OverlayReverseRow194
import ElevenSquare.Pending.S07_OverlayReverseRow195
import ElevenSquare.Pending.S07_OverlayReverseRow196
import ElevenSquare.Pending.S07_OverlayReverseRow197
import ElevenSquare.Pending.S07_OverlayReverseRow198
import ElevenSquare.Pending.S07_OverlayReverseRow199
import ElevenSquare.Pending.S07_OverlayReverseRow200
import ElevenSquare.Pending.S07_OverlayReverseRow201
import ElevenSquare.Pending.S07_OverlayReverseRow202
import ElevenSquare.Pending.S07_OverlayReverseRow203
import ElevenSquare.Pending.S07_OverlayReverseRow204
import ElevenSquare.Pending.S07_OverlayReverseRow205
import ElevenSquare.Pending.S07_OverlayReverseRow206
import ElevenSquare.Pending.S07_OverlayReverseRow207
import ElevenSquare.Pending.S07_OverlayReverseRow208
import ElevenSquare.Pending.S07_OverlayReverseRow209
import ElevenSquare.Pending.S07_OverlayReverseRow210
import ElevenSquare.Pending.S07_OverlayReverseRow211
import ElevenSquare.Pending.S07_OverlayReverseRow212
import ElevenSquare.Pending.S07_OverlayReverseRow213
import ElevenSquare.Pending.S07_OverlayReverseRow214
import ElevenSquare.Pending.S07_OverlayReverseRow215
import ElevenSquare.Pending.S07_OverlayReverseRow216
import ElevenSquare.Pending.S07_OverlayReverseRow217
import ElevenSquare.Pending.S07_OverlayReverseRow218
import ElevenSquare.Pending.S07_OverlayReverseRow219
namespace ElevenSquare.Pending.T04Reverse
open OverlayVertexChecks
open GridDistance
theorem reverse_aligned6 : ArrayAligned ReverseRowFits
    (recordedOverlayVerticesChunk12 ++ recordedOverlayVerticesChunk13) recordedOverlayLabelsChunk6 := by
  have hv : recordedOverlayVerticesChunk12 ++ recordedOverlayVerticesChunk13 = rationalChunk12 ++ rationalChunk13 := rfl
  rw [hv]
  change List.Forall₂ ReverseRowFits [rationalRow192, rationalRow193, rationalRow194, rationalRow195, rationalRow196, rationalRow197, rationalRow198, rationalRow199, rationalRow200, rationalRow201, rationalRow202, rationalRow203, rationalRow204, rationalRow205, rationalRow206, rationalRow207, rationalRow208, rationalRow209, rationalRow210, rationalRow211, rationalRow212, rationalRow213, rationalRow214, rationalRow215, rationalRow216, rationalRow217, rationalRow218, rationalRow219] [![13,10,5,7], ![13,10,9,6], ![13,13,4,11], ![13,14,0,7], ![13,14,4,7], ![13,14,4,11], ![13,15,0,7], ![13,15,4,7], ![14,12,8,11], ![14,12,8,15], ![14,13,4,11], ![14,13,8,11], ![14,13,8,15], ![14,14,4,7], ![14,14,4,11], ![14,14,8,11], ![15,8,8,10], ![15,8,8,15], ![15,8,12,10], ![15,8,12,14], ![15,8,12,15], ![15,8,13,10], ![15,8,13,14], ![15,8,13,15], ![15,12,8,15], ![15,12,12,15], ![15,13,8,11], ![15,13,8,15]]
  exact (List.Forall₂.cons overlay_in_hull192 (List.Forall₂.cons overlay_in_hull193 (List.Forall₂.cons overlay_in_hull194 (List.Forall₂.cons overlay_in_hull195 (List.Forall₂.cons overlay_in_hull196 (List.Forall₂.cons overlay_in_hull197 (List.Forall₂.cons overlay_in_hull198 (List.Forall₂.cons overlay_in_hull199 (List.Forall₂.cons overlay_in_hull200 (List.Forall₂.cons overlay_in_hull201 (List.Forall₂.cons overlay_in_hull202 (List.Forall₂.cons overlay_in_hull203 (List.Forall₂.cons overlay_in_hull204 (List.Forall₂.cons overlay_in_hull205 (List.Forall₂.cons overlay_in_hull206 (List.Forall₂.cons overlay_in_hull207 (List.Forall₂.cons overlay_in_hull208 (List.Forall₂.cons overlay_in_hull209 (List.Forall₂.cons overlay_in_hull210 (List.Forall₂.cons overlay_in_hull211 (List.Forall₂.cons overlay_in_hull212 (List.Forall₂.cons overlay_in_hull213 (List.Forall₂.cons overlay_in_hull214 (List.Forall₂.cons overlay_in_hull215 (List.Forall₂.cons overlay_in_hull216 (List.Forall₂.cons overlay_in_hull217 (List.Forall₂.cons overlay_in_hull218 (List.Forall₂.cons overlay_in_hull219 List.Forall₂.nil))))))))))))))))))))))))))))
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.reverse_aligned6
