import ElevenSquare.Pending.S07_GridRows0
import ElevenSquare.Pending.S07_GridRows1
import ElevenSquare.Pending.S07_GridRows2
import ElevenSquare.Pending.S07_GridRows3
import ElevenSquare.Pending.S07_GridRows4
import ElevenSquare.Pending.S07_GridRows5
import ElevenSquare.Pending.S07_GridRows6
import ElevenSquare.Pending.S07_GridRows7
import ElevenSquare.Pending.S07_GridRows8
import ElevenSquare.Pending.S07_GridRows9
import ElevenSquare.Pending.S07_GridRows10
import ElevenSquare.Pending.S07_GridRows11
import ElevenSquare.Pending.S07_GridRows12
import ElevenSquare.Pending.S07_GridRows13
namespace ElevenSquare.Pending.GridDistance
theorem full_alignment : ArrayAligned Row recordedOverlayVertices gridArray := by
  unfold recordedOverlayVertices gridArray
  exact (((((((((((((aligned_chunk0.append aligned_chunk1).append aligned_chunk2).append aligned_chunk3).append aligned_chunk4).append aligned_chunk5).append aligned_chunk6).append aligned_chunk7).append aligned_chunk8).append aligned_chunk9).append aligned_chunk10).append aligned_chunk11).append aligned_chunk12).append aligned_chunk13)
end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.full_alignment
