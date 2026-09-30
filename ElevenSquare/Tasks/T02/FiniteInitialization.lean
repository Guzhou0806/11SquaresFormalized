import ElevenSquare.Tasks.T02.ChartSubdivision
import ElevenSquare.Tasks.T02.Wall
import ElevenSquare.Tasks.T02.DirectOwnership

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- The halfplane implications cover the actual wall-clipped closed cell.
The vertex list is used only after its polygon check has been discharged. -/
structure CellRootCertificate (n : ℕ) where
  margin : Fin n → ℚ
  bounds : Fin n → List (Halfplane × BaselineCombination)
  vertices : Fin n → List QPoint
  owned : List QPoint

def CellRootCertificate.row {n : ℕ} (c : CellRootCertificate n) (b : Fin n) : PoseRow :=
  uniformRow n ((c.bounds b).map Prod.fst) b

def CellRootCertificate.rows {n : ℕ} (c : CellRootCertificate n) : List PoseRow :=
  (List.finRange n).map c.row

def CellRootCertificate.Check {n : ℕ} (cell : Fin 16) (c : CellRootCertificate n) : Prop :=
  ∀ b : Fin n,
    BaselineWallCheck (c.row b).lo (c.row b).hi (c.margin b) ∧
    (∀ e ∈ c.bounds b,
      BaselineImplicationCheck (baselineSlab cell (c.margin b)) e.1 e.2) ∧
    (∀ p ∈ c.owned, DirectPointCheck (c.row b) (c.vertices b) p)

instance cellRootCertificateCheckDecidable {n : ℕ} (cell : Fin 16) (c : CellRootCertificate n) :
    Decidable (c.Check cell) := by
  unfold CellRootCertificate.Check
  infer_instance

theorem cell_root_rows_cover {n : ℕ} (hn : 0 < n) (cell : Fin 16)
    (c : CellRootCertificate n) (hc : c.Check cell) (q : UnitSquare)
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
  have hslab := baseline_slab_contains q cell (c.row b).lo (c.row b).hi
    (c.margin b) t (hc b).1 hbl hbu ha hcont (baselineCellPolygon_contains hcell)
  refine ⟨c.row b, List.mem_map.mpr ⟨b, by simp, rfl⟩, ?_, t, ht0, ht1, hbl, hbu, ha⟩
  intro h hh
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hh
  exact baseline_implication_check_sound _ _ _ ((hc b).2.1 e he) q.center hslab

theorem cell_root_owned {n : ℕ} (cell : Fin 16) (c : CellRootCertificate n)
    (hc : c.Check cell) (q : UnitSquare) (hq : RowsContain c.rows q) :
    rationalHull c.owned ⊆ {p | OpenSquare q p} := by
  obtain ⟨r, hr, hcontains⟩ := hq
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
  apply hull_owned_of_vertices
  intro p hp
  exact directPointCheck_sound (c.row b) (c.vertices b) p ((hc b).2.2 p hp) q hcontains

def checkedSeedRoot {n : ℕ} (cs : Fin 16 → CellRootCertificate n)
    (m : Finset (Fin 16)) : PoseState where
  rows := fun i => (cs (baselineRoles m i)).rows
  owned := fun i => (cs (baselineRoles m i)).owned

/-- Literal root checks must be supplied for every occupied cell. This gives
the owner permutation required by the public certificate-existence contract. -/
theorem checked_seed_root_initialized {n : ℕ} (hn : 0 < n)
    (cs : Fin 16 → CellRootCertificate n) (m : Finset (Fin 16))
    (hchecks : ∀ cell ∈ m, (cs cell).Check cell)
    (P : Packing 11 coverCap) (hc : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) (checkedSeedRoot cs m) := by
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  have hcheck (i : Owner) : (cs (baselineRoles m i)).Check (baselineRoles m i) := by
    have hi : baselineRoles m i ∈ Finset.univ.image (baselineRoles m) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hi' : baselineRoles m i ∈ m :=
      Eq.mp (congrArg (fun cells => baselineRoles m i ∈ cells) (baselineRoles_image hm)) hi
    exact hchecks (baselineRoles m i) hi'
  have hrows (i : Owner) : RowsContain (cs (baselineRoles m i)).rows
      ((relabelPacking P perm).squares i) :=
    cell_root_rows_cover hn _ _ (hcheck i) _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))
  refine ⟨perm, hrows, ?_⟩
  intro i
  exact cell_root_owned _ _ (hcheck i) _ (hrows i)

end
end ElevenSquare.Tasks.T02
