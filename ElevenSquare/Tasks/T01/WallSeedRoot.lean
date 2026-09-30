import ElevenSquare.Tasks.T01.FiniteInitialization
import ElevenSquare.Tasks.T01.WallOwnership

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- The pose-cover discretization is independent of the finer ownership tree. -/
def CellRootCertificate.DomainCheck {n : ℕ} (cell : Fin 16)
    (c : CellRootCertificate n) : Prop :=
  ∀ b : Fin n, BaselineWallCheck (c.row b).lo (c.row b).hi (c.margin b) ∧
    ∀ e ∈ c.bounds b, BaselineImplicationCheck (baselineSlab cell (c.margin b)) e.1 e.2

instance cellRootDomainCheckDecidable {n : ℕ} (cell : Fin 16) (c : CellRootCertificate n) :
    Decidable (c.DomainCheck cell) := by
  unfold CellRootCertificate.DomainCheck
  infer_instance

theorem wall_seed_pose_cover {n : ℕ} (hn : 0 < n) (cell : Fin 16)
    (c : CellRootCertificate n) (hc : c.DomainCheck cell) (q : UnitSquare)
    (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    RowsContain c.rows q := by
  obtain ⟨t, ht0, ht1, ha⟩ := hchart
  obtain ⟨b, hl, hu⟩ := exists_uniform_bin n hn t ht0 ht1
  have hbl : ((c.row b).lo : ℝ) ≤ t := by
    simpa [CellRootCertificate.row, uniformRow] using hl
  have hbu : t ≤ ((c.row b).hi : ℝ) := by
    simpa [CellRootCertificate.row, uniformRow] using hu
  have hs := baseline_slab_contains q cell (c.row b).lo (c.row b).hi
    (c.margin b) t (hc b).1 hbl hbu ha hcont (baselineCellPolygon_contains hcell)
  refine ⟨c.row b, List.mem_map.mpr ⟨b, by simp, rfl⟩, ?_, t, ht0, ht1, hbl, hbu, ha⟩
  intro h hh
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hh
  exact baseline_implication_check_sound _ _ _ ((hc b).2 e he) q.center hs

theorem checked_wall_seed_root_initialized {n : ℕ} (hn : 0 < n)
    (cs : Fin 16 → CellRootCertificate n) (certs : Fin 16 → WallOwnershipCertificate)
    (m : Finset (Fin 16))
    (hdomains : ∀ cell ∈ m, (cs cell).DomainCheck cell)
    (hownership : ∀ cell ∈ m, (certs cell).Check cell (cs cell).owned 0 1)
    (P : Packing 11 coverCap) (hc : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) (checkedSeedRoot cs m) := by
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  have hmem (i : Owner) : baselineRoles m i ∈ m := by
    have hi : baselineRoles m i ∈ Finset.univ.image (baselineRoles m) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact Eq.mp (congrArg (fun cells => baselineRoles m i ∈ cells) (baselineRoles_image hm)) hi
  refine ⟨perm, ?_, ?_⟩
  · intro i
    exact wall_seed_pose_cover hn _ _ (hdomains _ (hmem i)) _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))
  · intro i
    exact checked_wall_owned_hull _ _ (certs (baselineRoles m i))
      (hownership _ (hmem i)) _ (hcell i) ((relabelPacking P perm).contained i) (hc (perm i))

end
end ElevenSquare.Tasks.T01
