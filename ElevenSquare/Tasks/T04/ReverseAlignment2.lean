import ElevenSquare.Tasks.T04.ReverseSupport
import ElevenSquare.Pending.S07_OverlayReverseRow64
import ElevenSquare.Pending.S07_OverlayReverseRow65
import ElevenSquare.Pending.S07_OverlayReverseRow66
import ElevenSquare.Pending.S07_OverlayReverseRow67
import ElevenSquare.Pending.S07_OverlayReverseRow68
import ElevenSquare.Pending.S07_OverlayReverseRow69
import ElevenSquare.Pending.S07_OverlayReverseRow70
import ElevenSquare.Pending.S07_OverlayReverseRow71
import ElevenSquare.Pending.S07_OverlayReverseRow72
import ElevenSquare.Pending.S07_OverlayReverseRow73
import ElevenSquare.Pending.S07_OverlayReverseRow74
import ElevenSquare.Pending.S07_OverlayReverseRow75
import ElevenSquare.Pending.S07_OverlayReverseRow76
import ElevenSquare.Pending.S07_OverlayReverseRow77
import ElevenSquare.Pending.S07_OverlayReverseRow78
import ElevenSquare.Pending.S07_OverlayReverseRow79
import ElevenSquare.Pending.S07_OverlayReverseRow80
import ElevenSquare.Pending.S07_OverlayReverseRow81
import ElevenSquare.Pending.S07_OverlayReverseRow82
import ElevenSquare.Pending.S07_OverlayReverseRow83
import ElevenSquare.Pending.S07_OverlayReverseRow84
import ElevenSquare.Pending.S07_OverlayReverseRow85
import ElevenSquare.Pending.S07_OverlayReverseRow86
import ElevenSquare.Pending.S07_OverlayReverseRow87
import ElevenSquare.Pending.S07_OverlayReverseRow88
import ElevenSquare.Pending.S07_OverlayReverseRow89
import ElevenSquare.Pending.S07_OverlayReverseRow90
import ElevenSquare.Pending.S07_OverlayReverseRow91
import ElevenSquare.Pending.S07_OverlayReverseRow92
import ElevenSquare.Pending.S07_OverlayReverseRow93
import ElevenSquare.Pending.S07_OverlayReverseRow94
import ElevenSquare.Pending.S07_OverlayReverseRow95
namespace ElevenSquare.Pending.T04Reverse
open OverlayVertexChecks
open GridDistance
theorem reverse_aligned2 : ArrayAligned ReverseRowFits
    (recordedOverlayVerticesChunk4 ++ recordedOverlayVerticesChunk5) recordedOverlayLabelsChunk2 := by
  have hv : recordedOverlayVerticesChunk4 ++ recordedOverlayVerticesChunk5 = rationalChunk4 ++ rationalChunk5 := rfl
  rw [hv]
  change List.Forall₂ ReverseRowFits [rationalRow64, rationalRow65, rationalRow66, rationalRow67, rationalRow68, rationalRow69, rationalRow70, rationalRow71, rationalRow72, rationalRow73, rationalRow74, rationalRow75, rationalRow76, rationalRow77, rationalRow78, rationalRow79, rationalRow80, rationalRow81, rationalRow82, rationalRow83, rationalRow84, rationalRow85, rationalRow86, rationalRow87, rationalRow88, rationalRow89, rationalRow90, rationalRow91, rationalRow92, rationalRow93, rationalRow94, rationalRow95] [![5,5,6,4], ![5,5,6,9], ![5,5,11,4], ![5,5,11,9], ![5,6,2,5], ![5,6,6,5], ![5,6,6,9], ![5,7,2,5], ![5,7,3,5], ![5,7,7,0], ![5,7,7,5], ![6,4,10,10], ![6,4,10,13], ![6,5,6,9], ![6,5,10,9], ![6,5,10,13], ![6,6,6,6], ![6,6,6,9], ![6,6,9,6], ![6,6,9,9], ![6,9,6,6], ![6,9,6,9], ![6,9,9,6], ![6,9,9,9], ![6,9,9,10], ![6,9,10,9], ![6,9,10,10], ![6,9,10,13], ![6,9,13,10], ![7,0,10,8], ![7,0,10,12], ![7,0,10,13]]
  exact (List.Forall₂.cons overlay_in_hull64 (List.Forall₂.cons overlay_in_hull65 (List.Forall₂.cons overlay_in_hull66 (List.Forall₂.cons overlay_in_hull67 (List.Forall₂.cons overlay_in_hull68 (List.Forall₂.cons overlay_in_hull69 (List.Forall₂.cons overlay_in_hull70 (List.Forall₂.cons overlay_in_hull71 (List.Forall₂.cons overlay_in_hull72 (List.Forall₂.cons overlay_in_hull73 (List.Forall₂.cons overlay_in_hull74 (List.Forall₂.cons overlay_in_hull75 (List.Forall₂.cons overlay_in_hull76 (List.Forall₂.cons overlay_in_hull77 (List.Forall₂.cons overlay_in_hull78 (List.Forall₂.cons overlay_in_hull79 (List.Forall₂.cons overlay_in_hull80 (List.Forall₂.cons overlay_in_hull81 (List.Forall₂.cons overlay_in_hull82 (List.Forall₂.cons overlay_in_hull83 (List.Forall₂.cons overlay_in_hull84 (List.Forall₂.cons overlay_in_hull85 (List.Forall₂.cons overlay_in_hull86 (List.Forall₂.cons overlay_in_hull87 (List.Forall₂.cons overlay_in_hull88 (List.Forall₂.cons overlay_in_hull89 (List.Forall₂.cons overlay_in_hull90 (List.Forall₂.cons overlay_in_hull91 (List.Forall₂.cons overlay_in_hull92 (List.Forall₂.cons overlay_in_hull93 (List.Forall₂.cons overlay_in_hull94 (List.Forall₂.cons overlay_in_hull95 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.reverse_aligned2
