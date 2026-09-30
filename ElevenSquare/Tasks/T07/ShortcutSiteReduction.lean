import ElevenSquare.Tasks.T07.ShortcutSiteSeed
import ElevenSquare.Tasks.T07.RoleAssignment

/-! Direct case-438 seed initialization with one point per occupied cell.
The point is inside the actual unit square for every chart orientation. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem occupied_has_siteSeed {S : ℝ} (P : Packing 11 S)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩)) :
    ∃ R : Packing 11 S, StateHolds R siteSeed ∧
      ∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i) := by
  obtain ⟨perm, hcell⟩ := occupied_has_owner_order P hocc
  let Q := relabelPacking P perm
  obtain ⟨R, t, ht, hsame⟩ := Q.exists_chart
  have hchartR : IsCharted R := by
    intro i
    exact ⟨t i, (ht i).1, (ht i).2.1, (ht i).2.2⟩
  have hcellR : ∀ i, ClosedCell (ownerCell i)
      (normalizeCenter (R.squares i).center) := by
    intro i
    rw [← (hsame i).center_eq]
    exact hcell i
  exact ⟨R, siteSeed_holds R hchartR hcellR, perm, hsame⟩

theorem occupied_has_siteSeed_centered {U V : ℝ} (P : Packing 11 U)
    (hocc : Occupies P (caseMask ⟨438, by omega⟩))
    (hsmall : CenteredPacking P V) :
    ∃ R : Packing 11 U, StateHolds R siteSeed ∧ CenteredPacking R V ∧
      ∃ perm : Equiv.Perm Owner,
        ∀ i, SameSquare (P.squares (perm i)) (R.squares i) := by
  obtain ⟨R, hseed, perm, hsame⟩ := occupied_has_siteSeed P hocc
  refine ⟨R, hseed, ?_, perm, hsame⟩
  intro i p hp
  exact hsmall (perm i) p (((hsame i).closed_iff p).mpr hp)

end
end ElevenSquare.Tasks.T07
