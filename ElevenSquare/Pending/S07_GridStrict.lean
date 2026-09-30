import ElevenSquare.Pending.S07_GridAlignment
import ElevenSquare.Pending.S07_GridAllPairs

namespace ElevenSquare.Pending.GridDistance

 theorem vertices_size : recordedOverlayVertices.size = 220 := by
  have h : recordedOverlayVertices.size = gridArray.size :=
    List.Forall₂.length_eq full_alignment
  exact h.trans grid_array_size

-- Traverse the fixed 220-record array; worker resource caps remain unchanged.
set_option maxRecDepth 2048 in
theorem overlay_row (r : Fin 220) : Row (overlayVertices r) gridArray[r.val]! := by
  unfold overlayVertices
  exact @ArrayAligned.get! (List QPoint) (List GridPoint) inferInstance inferInstance
    Row recordedOverlayVertices gridArray full_alignment r.val
    (by rw [vertices_size]; exact r.isLt)

 theorem listed_pair_strict (r s : Fin 220)
    (h : (r.val, s.val) ∈ bannedPairArray.toList) :
    ∀ p ∈ rationalHull (overlayVertices r), ∀ q ∈ rationalHull (overlayVertices s),
      (coverCap-1)^2 * normSq (p-q) < 1 := by
  apply hulls_strict
  have hc := all_bans_checked (r.val, s.val) h
  simp only [indexedCheck, Prod.fst, Prod.snd] at hc
  exact rows_bound (overlayVertices r) (overlayVertices s) gridArray[r.val]! gridArray[s.val]!
    (overlay_row r) (overlay_row s) (pairCheck_sound _ _ hc)

 theorem strict_bans (r s : Fin 220) (h : pairBanned r s) :
    ∀ p ∈ rationalHull (overlayVertices r), ∀ q ∈ rationalHull (overlayVertices s),
      (coverCap-1)^2 * normSq (p-q) < 1 := by
  rcases h with h | h
  · exact listed_pair_strict r s (List.mem_toFinset.mp h)
  · intro p hp q hq
    have hb := listed_pair_strict s r (List.mem_toFinset.mp h) q hq p hp
    have he : normSq (q-p) = normSq (p-q) := by
      dsimp [normSq, dot]
      ring
    rwa [he] at hb

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.strict_bans
