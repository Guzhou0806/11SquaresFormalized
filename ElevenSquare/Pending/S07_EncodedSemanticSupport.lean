import ElevenSquare.Pending.S07_EncodedData
import ElevenSquare.Pending.S07_BanMembershipSupport
import ElevenSquare.Pending.NatRangeCertificates
namespace ElevenSquare.Pending.EncodedSearch
def NeighborGood (r : ℕ) : Prop := ∀ s ∈ neighbors r, NatPairBanned r s
def LabelGood (r : ℕ) : Prop := ∀ g : Fin 4, label r g.val = (recordedOverlayLabels[r]! g).val
end ElevenSquare.Pending.EncodedSearch
