import ElevenSquare.Tasks.T02.Prior1000Initialization.DiskRoot
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell000.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell000.WallOwnership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell001.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell001.WallOwnership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell002.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell002.WallOwnership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell004.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell004.WallOwnership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell006.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell007.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell007.WallOwnership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell009.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell010.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell013.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell013.WallOwnership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell014.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell014.WallOwnership
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell015.PoseDomains
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell015.WallOwnership

namespace ElevenSquare.Tasks.T02.Prior1000Initialization
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

/-! The actual case-1000 archived initial state in physical coordinates.
The fixed increasing owner roles retain all 70 seed vertices and all 704 closed
pose rows. Ownership subdivisions are used only inside proofs; they do not alter
the archived 64-row pose discretization. -/

def poseCertificates (cell : Fin 16) : CellRootCertificate 64 :=
  match cell.val with
  | 0 => Cell000.poseCertificate
  | 1 => Cell001.poseCertificate
  | 2 => Cell002.poseCertificate
  | 4 => Cell004.poseCertificate
  | 6 => Cell006.poseCertificate
  | 7 => Cell007.poseCertificate
  | 9 => Cell009.poseCertificate
  | 10 => Cell010.poseCertificate
  | 13 => Cell013.poseCertificate
  | 14 => Cell014.poseCertificate
  | 15 => Cell015.poseCertificate
  | _ => Cell000.poseCertificate


theorem pose_domains_checked (i : Owner) : (poseCertificates (roles i)).DomainCheck (roles i) := by
  fin_cases i
  · exact Cell000.pose_domain_checked
  · exact Cell001.pose_domain_checked
  · exact Cell002.pose_domain_checked
  · exact Cell004.pose_domain_checked
  · exact Cell006.pose_domain_checked
  · exact Cell007.pose_domain_checked
  · exact Cell009.pose_domain_checked
  · exact Cell010.pose_domain_checked
  · exact Cell013.pose_domain_checked
  · exact Cell014.pose_domain_checked
  · exact Cell015.pose_domain_checked


theorem full_archived_hull_owned (i : Owner) (q : UnitSquare)
    (hcell : ClosedCell (roles i) (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    rationalHull (archivedOwned (roles i)) ⊆ {p | OpenSquare q p} := by
  fin_cases i
  · exact Cell000.full_hull_owned q hcell hcont hchart
  · exact Cell001.full_hull_owned q hcell hcont hchart
  · exact Cell002.full_hull_owned q hcell hcont hchart
  · exact Cell004.full_hull_owned q hcell hcont hchart
  · exact SeedCell006.initial_hull_owned q hcell
  · exact Cell007.full_hull_owned q hcell hcont hchart
  · exact SeedCell009.initial_hull_owned q hcell
  · exact SeedCell010.initial_hull_owned q hcell
  · exact Cell013.full_hull_owned q hcell hcont hchart
  · exact Cell014.full_hull_owned q hcell hcont hchart
  · exact Cell015.full_hull_owned q hcell hcont hchart


def archivedRoot : PoseState where
  rows := fun i => (poseCertificates (roles i)).rows
  owned := fun i => archivedOwned (roles i)


theorem archivedRoot_row_count (i : Owner) : (archivedRoot.rows i).length = 64 := by
  simp [archivedRoot, CellRootCertificate.rows]


theorem archivedRoot_owned_counts :
    (List.finRange 11).map (fun i => (archivedRoot.owned i).length) =
      [6, 5, 7, 8, 5, 10, 5, 6, 7, 5, 6] := by decide


theorem archivedRoot_owned_count :
    ((List.finRange 11).map (fun i => (archivedRoot.owned i).length)).sum = 70 := by decide


/-- The complete literal archived root for every actual charted packing in this
mask, including the permutation matching squares to the archived owner order. -/
theorem archived_root_initialized (P : Packing 11 coverCap)
    (hc : IsCharted P) (hocc : Occupies P mask) :
    ∃ perm : Equiv.Perm Owner,
      StateHolds (relabelPacking P perm) archivedRoot := by
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P roles roles_injective
    (roles_image.symm ▸ hocc)
  refine ⟨perm, ?_, ?_⟩
  · intro i
    exact wall_seed_pose_cover (by norm_num : 0 < 64) (roles i)
      (poseCertificates (roles i)) (pose_domains_checked i) _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))
  · intro i
    exact full_archived_hull_owned i _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))


end
end ElevenSquare.Tasks.T02.Prior1000Initialization
