import ElevenSquare.Tasks.T01.Field03Feature
import ElevenSquare.Tasks.T01.HalfTurnPacking

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G003
open ElevenSquare.Pending
noncomputable section

def supportCells : Fin 4 → Fin 16 := ![0,4,8,12]
def support : Finset (Fin 16) := {0,4,8,12}

/-- The geometric proof uses exactly these four occupied cells. The two
middle cells capture the same capacity-one majority feature. -/
def SupportCapture : Prop :=
  ∀ (P : Packing 11 coverCap), IsCharted P →
    ∀ (owners : Fin 4 → Owner), Function.Injective owners →
      (∀ c, ClosedCell (supportCells c) (normalizeCenter (P.squares (owners c)).center)) →
      BaselineMajorityCapture baselineField03Sites 2 (P.squares (owners 1)) ∧
      BaselineMajorityCapture baselineField03Sites 2 (P.squares (owners 2))

theorem exclusion_of_support_capture (hcap : SupportCapture)
    (m : Finset (Fin 16)) (hs : support ⊆ m)
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P m) : False := by
  classical
  obtain ⟨a, _, hm, hcell⟩ := ho
  have hmem (c : Fin 4) : supportCells c ∈ m := by
    apply hs
    fin_cases c <;> decide
  have hex (c : Fin 4) : ∃ i : Owner, a i = supportCells c := by
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
  have hclosed (c : Fin 4) :
      ClosedCell (supportCells c) (normalizeCenter (P.squares (owners c)).center) := by
    rw [← howners c]
    exact hcell (owners c)
  obtain ⟨hleft, hright⟩ := hcap P hc owners hinj hclosed
  exact baseline_field03_contradiction_of_two_captures P (owners 1) (owners 2)
    (fun h => (by decide : (1:Fin 4) ≠ 2) (hinj h)) hleft hright

theorem exclusion_of_support_or_halfTurn (hcap : SupportCapture)
    (m : Finset (Fin 16)) (hs : support ⊆ m ∨ support ⊆ halfTurnMask m)
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P m) : False :=
  charted_exclusion_of_support_or_halfTurn support m
    (exclusion_of_support_capture hcap) hs P hc ho

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.exclusion_of_support_or_halfTurn
