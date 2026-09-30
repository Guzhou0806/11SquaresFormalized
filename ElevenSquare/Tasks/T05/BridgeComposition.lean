import ElevenSquare.Tasks.T05.BridgeOverlay
import ElevenSquare.Tasks.T05.Masks

/-! Conditional bridge from the exact exclusion hypothesis to case438.
The packing family carries whole-square transport; only its normalized center
identity is used here. Owners remain unchanged throughout. -/
namespace ElevenSquare.Pending.T05Bridge
noncomputable section

theorem force_case438
    (hex : ∀ k : Fin 2184, k.val ∉ candidateIndices →
      ∀ R : Packing 11 coverCap, ¬ Occupies R (caseMask k))
    (P : Packing 11 coverCap)
    (Q : Fin 4 → Bool → Packing 11 coverCap)
    (hQ : ∀ g flip i, normalizeCenter ((Q g flip).squares i).center =
      (if flip then halfTurn else id) (view g (normalizeCenter (P.squares i).center))) :
    ∃ g : Fin 4, ∃ flip : Bool,
      Occupies (Q g flip) (caseMask ⟨438, by omega⟩) := by
  classical
  have cells : ∀ g : Fin 4, ∀ i : Owner, ∃ j : Fin 16,
      ClosedCell j (normalizeCenter ((Q g false).squares i).center) := by
    intro g i
    exact exists_closedCell _ (center_in_unit_box (Q g false) le_rfl i)
  choose a ha using cells
  have hinj (g : Fin 4) : Function.Injective (a g) := by
    intro i j hij
    exact closedCell_capacity (Q g false) (ha g i) (by rw [hij]; exact ha g j)
  let m : Fin 4 → CellMask := fun g => Finset.univ.image (a g)
  have hmcard (g : Fin 4) : (m g).card = 11 := by
    dsimp [m]
    rw [Finset.card_image_of_injective _ (hinj g)]
    simp
  have hocc (g : Fin 4) (flip : Bool) :
      Occupies (Q g flip) (if flip then ElevenSquare.halfTurnMask (m g) else m g) := by
    cases flip with
    | false => exact ⟨a g, hinj g, rfl, ha g⟩
    | true =>
      refine ⟨fun i => (a g i).rev, ?_, ?_, ?_⟩
      · intro i j hij
        exact hinj g (Fin.rev_inj.mp hij)
      · change Finset.univ.image (fun i => (a g i).rev) =
          (Finset.univ.image (a g)).image Fin.rev
        rw [Finset.image_image]
        rfl
      · intro i
        have hc : normalizeCenter ((Q g true).squares i).center =
            turnPoint (normalizeCenter ((Q g false).squares i).center) := by
          rw [hQ g true i, hQ g false i]
          rfl
        rw [hc]
        exact closedCell_halfTurn (ha g i)
  by_contra hnone
  have hnot (g : Fin 4) (flip : Bool) :
      ¬ Occupies (Q g flip) (caseMask ⟨438, by omega⟩) := by
    intro ht
    exact hnone ⟨g, flip, ht⟩
  have hraw (g : Fin 4) : m g ∈ otherRawMasks := by
    obtain ⟨flip, k, hk⟩ := T05Masks.canonical_case (m g) (hmcard g)
    have hok : Occupies (Q g flip) (caseMask k) := by
      rw [hk]
      exact hocc g flip
    have hcandidate : k.val ∈ candidateIndices := by
      by_contra hn
      exact hex k hn (Q g flip) hok
    have hne : k.val ≠ 438 := by
      intro hv
      have he : k = ⟨438, by omega⟩ := Fin.ext hv
      rw [he] at hok
      exact hnot g flip hok
    exact T05Masks.other_raw_of_canonical (m g) flip k hk hcandidate hne
  apply not_all_other_raw P a ?_ hinj hraw
  intro g i
  have hi := ha g i
  rw [hQ g false i] at hi
  exact hi

end
end ElevenSquare.Pending.T05Bridge
#print axioms ElevenSquare.Pending.T05Bridge.force_case438
