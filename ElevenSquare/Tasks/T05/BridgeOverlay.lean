import ElevenSquare.Pending.S07_Overlay
import ElevenSquare.Pending.S07_DistanceBans
import ElevenSquare.Pending.S07_FiniteSearch

/-! Independent closed-cell choices are transported to the exact overlay
inventory. Separation of the original packing excludes every banned pair. -/
namespace ElevenSquare.Pending.T05Bridge
noncomputable section

theorem no_banned_pair (P : Packing 11 coverCap) (f : Owner → Fin 220)
    (hf : ∀ i, normalizeCenter (P.squares i).center ∈ rationalHull (overlayVertices (f i)))
    (i j : Owner) (hij : i ≠ j) : ¬ pairBanned (f i) (f j) := by
  intro hb
  have hs := P.center_separation i j hij
  rw [normSq_sub_eq_distance, normalized_distance] at hs
  have hd := recorded_bans_strict (f i) (f j) hb
    (normalizeCenter (P.squares i).center) (hf i)
    (normalizeCenter (P.squares j).center) (hf j)
  rw [normSq_sub_eq_distance] at hd
  exact (not_lt_of_ge hs) hd

theorem not_all_other_raw (P : Packing 11 coverCap)
    (a : Fin 4 → Owner → Fin 16)
    (ha : ∀ g i, ClosedCell (a g i) (view g (normalizeCenter (P.squares i).center)))
    (hinj : ∀ g, Function.Injective (a g))
    (hm : ∀ g, Finset.univ.image (a g) ∈ otherRawMasks) : False := by
  have hov (i : Owner) := point_has_overlay (normalizeCenter (P.squares i).center)
    (fun g => a g i) (fun g => ha g i)
  choose f hf using hov
  apply finite_no_avoiding_assignment
  refine ⟨f, ?_, ?_, ?_⟩
  · intro g i j hij
    apply hinj g
    have hi := congrFun (hf i).2 g
    have hj := congrFun (hf j).2 g
    exact hi.symm.trans (hij.trans hj)
  · intro g
    have he : (fun i => overlayLabels (f i) g) = a g := by
      funext i
      exact congrFun (hf i).2 g
    rw [he]
    exact hm g
  · exact no_banned_pair P f (fun i => (hf i).1)

end
end ElevenSquare.Pending.T05Bridge
#print axioms ElevenSquare.Pending.T05Bridge.no_banned_pair
#print axioms ElevenSquare.Pending.T05Bridge.not_all_other_raw
