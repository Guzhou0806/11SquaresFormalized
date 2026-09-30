import ElevenSquare.Tasks.T01.WallSeedRoot

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A wall-clipped root may use pointwise ownership proofs checked independently
of its (possibly coarser) pose rows. The archived root's owned points are all
among the shared field ownership points, so this avoids duplicating their
angle trees in a `WallOwnershipCertificate`. -/
theorem initialized_from_domains_and_points {n : ℕ} (hn : 0 < n)
    (cs : Fin 16 → CellRootCertificate n) (m : Finset (Fin 16))
    (hdomains : ∀ cell ∈ m, (cs cell).DomainCheck cell)
    (hpoints : ∀ cell ∈ m, ∀ q : UnitSquare,
      ClosedCell cell (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      ∀ p ∈ (cs cell).owned, OpenSquare q (realPoint p))
    (P : Packing 11 coverCap) (hc : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner,
      StateHolds (relabelPacking P perm) (checkedSeedRoot cs m) := by
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  have hmem (i : Owner) : baselineRoles m i ∈ m := by
    have hi : baselineRoles m i ∈ Finset.univ.image (baselineRoles m) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact Eq.mp (congrArg (fun cells => baselineRoles m i ∈ cells)
      (baselineRoles_image hm)) hi
  refine ⟨perm, ?_, ?_⟩
  · intro i
    exact wall_seed_pose_cover hn _ _ (hdomains _ (hmem i)) _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))
  · intro i
    exact hull_owned_of_vertices _ _
      (hpoints _ (hmem i) _ (hcell i)
        ((relabelPacking P perm).contained i) (hc (perm i)))

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.initialized_from_domains_and_points
