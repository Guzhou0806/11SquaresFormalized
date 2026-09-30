import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Capacity
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.TransferCases
import ElevenSquare.Tasks.T01.HalfTurnPacking

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending
noncomputable section

def captureCells : Fin 3 → Fin 16 := ![5, 9, 10]

/-- The owners supplied by occupancy for the nine support cells. -/
def SupportOwners (P : Packing 11 coverCap) (owners : Fin 16 → Owner) : Prop :=
  (∀ c ∈ support, ClosedCell c (normalizeCenter (P.squares (owners c)).center)) ∧
    ∀ c ∈ support, ∀ d ∈ support, c ≠ d → owners c ≠ owners d

def CaptureChoice (q : UnitSquare) : Prop :=
  OpenSquare q (realPoint point) ∨ BaselineMajorityCapture sites 2 q

/-- Each of the three required squares captures one of the two capacity-one features. -/
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

theorem exclusion_of_capture (hcap : SupportCapture)
    (k : Fin 2184) (hk : k.val ∈ groupCases (7 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  charted_exclusion_of_support_or_halfTurn support (caseMask k)
    (exclusion_of_support_capture hcap) (public_support k hk) P hc ho

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.exclusion_of_capture
