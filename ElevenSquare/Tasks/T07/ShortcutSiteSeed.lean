import ElevenSquare.Tasks.T07.ShortcutSiteCore
import ElevenSquare.Tasks.T07.RoleAssignmentFinite

/-! The generic site-owned seed specialized to the ascending case-438 owners. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def siteSeed : PoseState := siteSeedFor ownerCell

theorem siteSeed_holds {S : ℝ} (P : Packing 11 S)
    (hchart : IsCharted P)
    (hcell : ∀ i, ClosedCell (ownerCell i)
      (normalizeCenter (P.squares i).center)) :
    StateHolds P siteSeed :=
  siteSeedFor_holds P ownerCell hchart hcell

end
end ElevenSquare.Tasks.T07
