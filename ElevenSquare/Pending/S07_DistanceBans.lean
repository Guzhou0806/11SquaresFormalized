import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridStrict
import ElevenSquare.Pending.S07_HullDistance
import ElevenSquare.Pending.S07_BanCount

/-! Exact distance certificates for the original recorded banned pairs. -/

namespace ElevenSquare.Pending
noncomputable section

-- Convex-hull extension is proved in S07_HullDistance, including empty hulls.
theorem recorded_bans_strict (r s : Fin 220) (h : pairBanned r s) :
    ∀ p ∈ rationalHull (overlayVertices r),
      ∀ q ∈ rationalHull (overlayVertices s),
        (coverCap-1)^2 * normSq (p-q) < 1 := by
  exact GridDistance.strict_bans r s h

-- The exact count is proved by ordered small blocks in S07_BanCount.


end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.squared_distance_on_hulls

#print axioms ElevenSquare.Pending.recorded_bans_count

#print axioms ElevenSquare.Pending.recorded_bans_strict
