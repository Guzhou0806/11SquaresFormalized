import ElevenSquare.Tasks.T01.CaptureCover
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SharedRosterBlockers

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedFeatureRow
open ElevenSquare Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A fixed row either captures one listed majority feature or places a
blocker in the current square. -/
inductive Target (n : ℕ) where
  | majority (feature : Fin n) (polygon : Polygon)
  | blocker (point : QPoint) (piece : FeatureCapturePiece)

def Target.polygon {n : ℕ} : Target n → Polygon
  | .majority _ polygon => polygon
  | .blocker _ piece => piece.polygon

def Target.blockerPoint {n : ℕ} : Target n → Option QPoint
  | .majority _ _ => none
  | .blocker point _ => some point

/-- Majority semantics are supplied as an explicit mathematical proof. The
blocker branch is certified by the finite feature-capture checker. -/
def Target.Check {n : ℕ} (family : Fin n → Finset QPoint)
    (threshold : Fin n → ℕ) (row : PoseRow) : Target n → Prop
  | .majority feature polygon =>
      ∀ q : UnitSquare, row.contains q → q.center ∈ polygon.carrier →
        BaselineMajorityCapture (family feature) (threshold feature) q
  | .blocker point piece => piece.Check [point] row

structure Certificate (n : ℕ) where
  targets : List (Target n)
  cover : BaselineCoverCertificate

def Certificate.polygons {n : ℕ} (cert : Certificate n) : List Polygon :=
  cert.targets.map Target.polygon

def Certificate.blockerPoints {n : ℕ} (cert : Certificate n) : List QPoint :=
  cert.targets.filterMap Target.blockerPoint

def Certificate.Check {n : ℕ} (cert : Certificate n)
    (family : Fin n → Finset QPoint) (threshold : Fin n → ℕ)
    (row : PoseRow) : Prop :=
  cert.cover.Check row.centers cert.polygons ∧
    ∀ target ∈ cert.targets, target.Check family threshold row

theorem row_choice {n : ℕ} (cert : Certificate n)
    (family : Fin n → Finset QPoint) (threshold : Fin n → ℕ)
    (row : PoseRow) (hcert : cert.Check family threshold row)
    (q : UnitSquare) (hq : row.contains q)
    (hblocked : ∀ p ∈ cert.blockerPoints,
      ¬ OpenSquare q (realPoint p)) :
    ∃ feature : Fin n,
      BaselineMajorityCapture (family feature) (threshold feature) q := by
  obtain ⟨polygon, hpolygon, hcenter⟩ :=
    baseline_cover_certificate_sound row.centers cert.polygons
      cert.cover hcert.1 q.center hq.1
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hpolygon
  have htargetCheck := hcert.2 target htarget
  cases target with
  | majority feature polygon =>
      exact ⟨feature, htargetCheck q hq hcenter⟩
  | blocker point piece =>
      have hp : point ∈ cert.blockerPoints := by
        unfold Certificate.blockerPoints
        exact (List.mem_filterMap Target.blockerPoint cert.targets).mpr
          ⟨Target.blocker point piece, htarget, rfl⟩
      exact False.elim ((hblocked point hp)
        (singleton_capture point q
          (feature_capture_piece_sound [point] row piece
            htargetCheck q hq hcenter)))

theorem packing_row_choice {n : ℕ} (cert : Certificate n)
    (family : Fin n → Finset QPoint) (threshold : Fin n → ℕ)
    (row : PoseRow) (hcert : cert.Check family threshold row)
    (P : Packing 11 coverCap) (i : Owner)
    (hq : row.contains (P.squares i))
    (howned : ∀ p ∈ cert.blockerPoints,
      ∃ j : Owner, i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    ∃ feature : Fin n,
      BaselineMajorityCapture (family feature) (threshold feature)
        (P.squares i) := by
  apply row_choice cert family threshold row hcert (P.squares i) hq
  intro p hp ho
  obtain ⟨j, hij, hj⟩ := howned p hp
  exact P.interior_disjoint i j hij (realPoint p) ⟨ho, hj⟩

/-- Convenient specialization when numeric blockers are shared-roster gate
indices. Equality with the certificate blocker list remains an exact Lean
obligation for each concrete row. -/
theorem packing_row_choice_of_roster {n : ℕ} (cert : Certificate n)
    (family : Fin n → Finset QPoint) (threshold : Fin n → ℕ)
    (row : PoseRow) (hcert : cert.Check family threshold row)
    (P : Packing 11 coverCap) (hc : IsCharted P) (i : Owner)
    (hq : row.contains (P.squares i))
    (partner : Fin 16 → Owner) (indices : List (Fin 16 × ℕ))
    (hpoints : cert.blockerPoints = SharedRosterBlockers.pointsOfRosterIndices indices)
    (hne : ∀ item ∈ indices, i ≠ partner item.1)
    (hcell : ∀ item ∈ indices,
      ClosedCell item.1
        (normalizeCenter (P.squares (partner item.1)).center))
    (hindex : ∀ item ∈ indices,
      item.2 < (SharedFieldOwnership.sharedRoster item.1).length) :
    ∃ feature : Fin n,
      BaselineMajorityCapture (family feature) (threshold feature)
        (P.squares i) := by
  apply packing_row_choice cert family threshold row hcert P i hq
  rw [hpoints]
  exact SharedRosterBlockers.roster_index_points_owned P hc i partner indices
    hne hcell hindex

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedFeatureRow

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedFeatureRow.packing_row_choice_of_roster
