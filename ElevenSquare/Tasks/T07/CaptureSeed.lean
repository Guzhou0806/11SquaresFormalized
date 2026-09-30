import ElevenSquare.Tasks.T07.CaptureSeedGeometry
import ElevenSquare.Tasks.T07.RoleAssignment

namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def occupiedCellSeed : PoseState where
  rows i := [{ lo := 0, hi := 1, centers := seedCellPolygon (ownerCell i) }]
  owned _ := []

/-- Each occupied case-438 packing has an owner-ordered, charted physical
representative satisfying the exact closed-cell root state. -/
theorem occupied_has_seed {S : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩)) :
    ∃ R : Packing 11 S, StateHolds R occupiedCellSeed ∧
      ∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i) := by
  obtain ⟨perm, hcell⟩ := occupied_has_owner_order P hocc
  let Q := relabelPacking P perm
  obtain ⟨R, ts, hts, hsame⟩ := Q.exists_chart
  refine ⟨R, ?_, perm, ?_⟩
  · constructor
    · intro i
      let t := ts i
      have ht0 := (hts i).1
      have ht1 := (hts i).2.1
      have haxis := (hts i).2.2
      refine ⟨{ lo := 0, hi := 1, centers := seedCellPolygon (ownerCell i) },
        by simp [occupiedCellSeed], ?_⟩
      refine ⟨?_, t, ht0, ht1, ?_, ?_, haxis⟩
      · apply seedCellPolygon_sound
        rw [← (hsame i).center_eq]
        exact hcell i
      · simpa using ht0
      · simpa using ht1
    · intro i
      simp [occupiedCellSeed, rationalHull]
  · intro i
    exact hsame i

end
end ElevenSquare.Tasks.T07
