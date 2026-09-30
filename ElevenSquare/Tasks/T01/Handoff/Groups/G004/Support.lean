import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FeatureData
import ElevenSquare.Tasks.T01.HalfTurnPacking

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004
open ElevenSquare.Pending
noncomputable section

def supportCells : Fin 5 → Fin 16 := ![0, 1, 2, 3, 6]
def support : Finset (Fin 16) := {0, 1, 2, 3, 6}

/-- The continuous geometric obligation for this group. The other three
    occupied cells can supply blocker information in its proof. -/
def SupportCapture : Prop :=
  ∀ (P : Packing 11 coverCap), IsCharted P →
    ∀ (owners : Fin 5 → Owner), Function.Injective owners →
      (∀ c, ClosedCell (supportCells c)
        (normalizeCenter (P.squares (owners c)).center)) →
      BaselineMajorityCapture featureSites 3 (P.squares (owners 1)) ∧
      BaselineMajorityCapture featureSites 3 (P.squares (owners 2))

theorem exclusion_of_support_capture (hcap : SupportCapture)
    (m : Finset (Fin 16)) (hs : support ⊆ m)
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P m) : False := by
  classical
  obtain ⟨a, _, hm, hcell⟩ := ho
  have hmem (c : Fin 5) : supportCells c ∈ m := by
    apply hs
    fin_cases c <;> decide
  have hex (c : Fin 5) : ∃ i : Owner, a i = supportCells c := by
    have h := hmem c
    rw [← hm] at h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact ⟨i, hi⟩
  choose owners howners using hex
  have hinj : Function.Injective owners := by
    intro c d he
    have hsc : supportCells c = supportCells d := by
      rw [← howners c, ← howners d, he]
    have hi : Function.Injective supportCells := by decide
    exact hi hsc
  have hclosed (c : Fin 5) :
      ClosedCell (supportCells c)
        (normalizeCenter (P.squares (owners c)).center) := by
    rw [← howners c]
    exact hcell (owners c)
  obtain ⟨hleft, hright⟩ := hcap P hc owners hinj hclosed
  exact (by decide : (1 : Fin 5) ≠ 2)
    (hinj (feature_capacity P (owners 1) (owners 2) hleft hright))

theorem exclusion_of_support_or_halfTurn (hcap : SupportCapture)
    (m : Finset (Fin 16)) (hs : support ⊆ m ∨ support ⊆ halfTurnMask m)
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P m) : False :=
  charted_exclusion_of_support_or_halfTurn support m
    (exclusion_of_support_capture hcap) hs P hc ho

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.exclusion_of_support_or_halfTurn
