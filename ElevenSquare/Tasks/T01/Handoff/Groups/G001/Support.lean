import ElevenSquare.Tasks.T01.Handoff.Groups.G001.FeatureData
import ElevenSquare.Tasks.T01.HalfTurnPacking

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G001
open ElevenSquare.Pending
noncomputable section

/-- The seven occupied cells used by the archived mask-2147 feature packet. -/
def support : Finset (Fin 16) := {1, 2, 4, 5, 6, 7, 11}
def captureCells : Fin 3 → Fin 16 := ![1, 5, 6]

def SupportOwners (P : Packing 11 coverCap) (owners : Fin 16 → Owner) : Prop :=
  (∀ c ∈ support, ClosedCell c (normalizeCenter (P.squares (owners c)).center)) ∧
    ∀ c ∈ support, ∀ d ∈ support, c ≠ d → owners c ≠ owners d

def CaptureChoice (q : UnitSquare) : Prop :=
  BaselineMajorityCapture featureA 3 q ∨ BaselineMajorityCapture featureB 2 q

/-- The geometric premise to be discharged by the three fixed-core cell captures. -/
def SupportCapture : Prop :=
  ∀ (P : Packing 11 coverCap), IsCharted P →
    ∀ (owners : Fin 16 → Owner), SupportOwners P owners →
      ∀ j : Fin 3, CaptureChoice (P.squares (owners (captureCells j)))

theorem capture_cell_mem_support (j : Fin 3) : captureCells j ∈ support := by
  fin_cases j <;> decide

theorem exclusion_of_support_capture (hcap : SupportCapture)
    (m : Finset (Fin 16)) (hs : support ⊆ m)
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P m) : False := by
  classical
  obtain ⟨a, _, hm, hcell⟩ := ho
  have hex (c : Fin 16) : ∃ i : Owner, c ∈ support → a i = c := by
    by_cases hcs : c ∈ support
    · have hcm := hs hcs
      rw [← hm] at hcm
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hcm
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => (hcs h).elim⟩
  choose owners howners using hex
  have hsupport : SupportOwners P owners := by
    constructor
    · intro c hcs
      simpa only [howners c hcs] using hcell (owners c)
    · intro c hcs d hds hcd he
      apply hcd
      rw [← howners c hcs, ← howners d hds, he]
  apply three_captures_impossible P (fun j => owners (captureCells j))
  · intro j k he
    have hcells : captureCells j = captureCells k := by
      by_contra hne
      exact hsupport.2 _ (capture_cell_mem_support j) _
        (capture_cell_mem_support k) hne he
    exact (by decide : Function.Injective captureCells) hcells
  · exact hcap P hc owners hsupport

theorem exclusion_of_support_or_halfTurn (hcap : SupportCapture)
    (m : Finset (Fin 16)) (hs : support ⊆ m ∨ support ⊆ halfTurnMask m)
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P m) : False :=
  charted_exclusion_of_support_or_halfTurn support m
    (exclusion_of_support_capture hcap) hs P hc ho

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G001

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G001.exclusion_of_support_or_halfTurn
