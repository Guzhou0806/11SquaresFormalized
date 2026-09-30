import ElevenSquare.Pending.S07_OverlayVertexSupport

namespace ElevenSquare.Pending.T04Alignment
open GridDistance

/-- Assemble arbitrary chunks before substituting the large recorded tables. -/
theorem append_fourteen {α β : Type} (P : α → β → Prop)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : Array α)
    (b0 b1 b2 b3 b4 b5 b6 : Array β)
    (h0 : ArrayAligned P (a0 ++ a1) b0)
    (h1 : ArrayAligned P (a2 ++ a3) b1)
    (h2 : ArrayAligned P (a4 ++ a5) b2)
    (h3 : ArrayAligned P (a6 ++ a7) b3)
    (h4 : ArrayAligned P (a8 ++ a9) b4)
    (h5 : ArrayAligned P (a10 ++ a11) b5)
    (h6 : ArrayAligned P (a12 ++ a13) b6)
    : ArrayAligned P (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13)
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6) := by
  simpa only [Array.append_assoc] using
    ((((((h0.append h1).append h2).append h3).append h4).append h5).append h6)

end ElevenSquare.Pending.T04Alignment
