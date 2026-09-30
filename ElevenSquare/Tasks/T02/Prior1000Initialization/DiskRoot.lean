import ElevenSquare.Tasks.T02.ChartSubdivision
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell000.Ownership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell001.Ownership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell002.Ownership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell004.Ownership
import ElevenSquare.Tasks.T02.SeedCell006.Ownership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell007.Ownership
import ElevenSquare.Tasks.T02.SeedCell009.Ownership
import ElevenSquare.Tasks.T02.SeedCell010.Ownership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell013.Ownership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell014.Ownership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell015.Ownership

namespace ElevenSquare.Tasks.T02.Prior1000Initialization
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

/-! A concrete, checked checkpoint for the archived case-1000 initial state.
All 26 disk-owned archive vertices are present. The remaining 44 wall-owned
vertices and the wall-clipped historical pose domains are separate obligations.
This is not the complete archived root or a case exclusion. -/

def roles : Owner → Fin 16 := ![0, 1, 2, 4, 6, 7, 9, 10, 13, 14, 15]
def mask : Finset (Fin 16) := {0, 1, 2, 4, 6, 7, 9, 10, 13, 14, 15}

theorem roles_injective : Function.Injective roles := by decide

theorem roles_image : Finset.univ.image roles = mask := by decide

def diskOwned (cell : Fin 16) : List QPoint :=
  match cell.val with
  | 0 => Cell000.diskOwned
  | 1 => Cell001.diskOwned
  | 2 => Cell002.diskOwned
  | 4 => Cell004.diskOwned
  | 6 => SeedCell006.owned
  | 7 => Cell007.diskOwned
  | 9 => SeedCell009.owned
  | 10 => SeedCell010.owned
  | 13 => Cell013.diskOwned
  | 14 => Cell014.diskOwned
  | 15 => Cell015.diskOwned
  | _ => []

def archivedOwned (cell : Fin 16) : List QPoint :=
  match cell.val with
  | 0 => Cell000.archivedOwned
  | 1 => Cell001.archivedOwned
  | 2 => Cell002.archivedOwned
  | 4 => Cell004.archivedOwned
  | 6 => SeedCell006.owned
  | 7 => Cell007.archivedOwned
  | 9 => SeedCell009.owned
  | 10 => SeedCell010.owned
  | 13 => Cell013.archivedOwned
  | 14 => Cell014.archivedOwned
  | 15 => Cell015.archivedOwned
  | _ => []

theorem disk_subset_archived (cell : Fin 16) :
    ∀ p ∈ diskOwned cell, p ∈ archivedOwned cell := by
  fin_cases cell
  · exact Cell000.disk_subset_archived
  · exact Cell001.disk_subset_archived
  · exact Cell002.disk_subset_archived
  · simp [diskOwned, archivedOwned]
  · exact Cell004.disk_subset_archived
  · simp [diskOwned, archivedOwned]
  · simp [diskOwned, archivedOwned]
  · exact Cell007.disk_subset_archived
  · simp [diskOwned, archivedOwned]
  · simp [diskOwned, archivedOwned]
  · simp [diskOwned, archivedOwned]
  · simp [diskOwned, archivedOwned]
  · simp [diskOwned, archivedOwned]
  · exact Cell013.disk_subset_archived
  · exact Cell014.disk_subset_archived
  · exact Cell015.disk_subset_archived

theorem disk_hull_owned (cell : Fin 16) (q : UnitSquare)
    (hcell : ClosedCell cell (normalizeCenter q.center)) :
    rationalHull (diskOwned cell) ⊆ {p | OpenSquare q p} := by
  fin_cases cell
  · exact Cell000.disk_hull_owned q hcell
  · exact Cell001.disk_hull_owned q hcell
  · exact Cell002.disk_hull_owned q hcell
  · simp [diskOwned, rationalHull]
  · exact Cell004.disk_hull_owned q hcell
  · simp [diskOwned, rationalHull]
  · exact SeedCell006.initial_hull_owned q hcell
  · exact Cell007.disk_hull_owned q hcell
  · simp [diskOwned, rationalHull]
  · exact SeedCell009.initial_hull_owned q hcell
  · exact SeedCell010.initial_hull_owned q hcell
  · simp [diskOwned, rationalHull]
  · simp [diskOwned, rationalHull]
  · exact Cell013.disk_hull_owned q hcell
  · exact Cell014.disk_hull_owned q hcell
  · exact Cell015.disk_hull_owned q hcell

def diskRoot : PoseState where
  rows := fun i => uniformRows 64 (baselineCellPolygon (roles i))
  owned := fun i => diskOwned (roles i)

/-- Existential relabeling of actual packings, with all closed chart seams kept.
Only the documented disk subset of the archive is initialized here. -/
theorem disk_root_initialized {S : ℝ} (P : Packing 11 S)
    (hc : IsCharted P) (hocc : Occupies P mask) :
    ∃ perm : Equiv.Perm Owner,
      StateHolds (relabelPacking P perm) diskRoot := by
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P roles roles_injective
    (roles_image.symm ▸ hocc)
  refine ⟨perm, ?_, ?_⟩
  · intro i
    apply (uniformRows_contains 64 (by norm_num) _ _).mpr
    exact ⟨baselineCellPolygon_contains (hcell i), hc (perm i)⟩
  · intro i
    exact disk_hull_owned (roles i) _ (hcell i)

end
end ElevenSquare.Tasks.T02.Prior1000Initialization
