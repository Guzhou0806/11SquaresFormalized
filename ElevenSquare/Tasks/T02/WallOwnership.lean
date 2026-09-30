import ElevenSquare.Tasks.T02.Wall
import ElevenSquare.Tasks.T02.DirectOwnership
import ElevenSquare.Pending.S06_BaselineCoverCertificate

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

structure WallOwnershipLeaf where
  margin : ℚ
  polygon : Polygon
  vertices : List QPoint
  implications : List BaselineCombination

def WallOwnershipLeaf.Check (cell : Fin 16) (points : List QPoint) (lo hi : ℚ)
    (leaf : WallOwnershipLeaf) : Prop :=
  BaselineWallCheck lo hi leaf.margin ∧
  BaselinePolygonImplicationCheck (baselineSlab cell leaf.margin)
    leaf.polygon leaf.implications ∧
  ∀ p ∈ points, DirectPointCheck ⟨lo, hi, leaf.polygon⟩ leaf.vertices p

instance wallOwnershipLeafCheckDecidable (cell : Fin 16) (points : List QPoint)
    (lo hi : ℚ) (leaf : WallOwnershipLeaf) : Decidable (leaf.Check cell points lo hi) := by
  unfold WallOwnershipLeaf.Check
  infer_instance

/-- Ownership may require finer angle subdivisions than the pose-state rows.
Both sides of every split keep the seam. No leaf can ignore container walls. -/
inductive WallOwnershipCertificate where
  | leaf (data : WallOwnershipLeaf)
  | empty (margin : ℚ) (witness : BaselineCombination)
  | split (cut : ℚ) (left right : WallOwnershipCertificate)

def WallOwnershipCertificate.Check (cell : Fin 16) (points : List QPoint)
    (lo hi : ℚ) : WallOwnershipCertificate → Prop
  | .leaf data => data.Check cell points lo hi
  | .empty margin w => BaselineWallCheck lo hi margin ∧
      BaselineStrictImplicationCheck (baselineSlab cell margin) baselineZeroHalfplane w
  | .split cut left right => lo ≤ cut ∧ cut ≤ hi ∧
      left.Check cell points lo cut ∧ right.Check cell points cut hi

instance wallOwnershipCheckDecidable (cell : Fin 16) (points : List QPoint)
    (lo hi : ℚ) (cert : WallOwnershipCertificate) :
    Decidable (cert.Check cell points lo hi) := by
  induction cert generalizing lo hi with
  | leaf data => exact inferInstanceAs (Decidable (data.Check cell points lo hi))
  | empty margin w => exact inferInstanceAs (Decidable (_ ∧ _))
  | split cut left right ihl ihr =>
    letI := ihl lo cut
    letI := ihr cut hi
    exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem wall_ownership_sound (cell : Fin 16) (points : List QPoint)
    (cert : WallOwnershipCertificate) (lo hi : ℚ) (hc : cert.Check cell points lo hi)
    (q : UnitSquare) (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : (lo : ℝ) ≤ t) (hu : t ≤ (hi : ℝ)) :
    ∀ p ∈ points, OpenSquare q (realPoint p) := by
  induction cert generalizing lo hi with
  | leaf data =>
    have hs := baseline_slab_contains q cell lo hi data.margin t hc.1 hl hu ha
      hcont (baselineCellPolygon_contains hcell)
    have hp := baseline_polygon_implication_check_sound _ _ _ hc.2.1 hs
    intro p hmem
    exact directPointCheck_sound _ data.vertices p (hc.2.2 p hmem) q
      ⟨hp, t, ht0, ht1, hl, hu, ha⟩
  | empty margin w =>
    have hs := baseline_slab_contains q cell lo hi margin t hc.1 hl hu ha
      hcont (baselineCellPolygon_contains hcell)
    have hf := baseline_strict_implication_check_sound _ _ w hc.2 q.center hs
    norm_num [baselineZeroHalfplane] at hf
  | split cut left right ihl ihr =>
    by_cases hcut : t ≤ (cut : ℝ)
    · exact ihl lo cut hc.2.2.1 hl hcut
    · exact ihr cut hi hc.2.2.2 (le_of_not_ge hcut) hu

theorem checked_wall_owned_hull (cell : Fin 16) (points : List QPoint)
    (cert : WallOwnershipCertificate) (hc : cert.Check cell points 0 1)
    (q : UnitSquare) (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    rationalHull points ⊆ {p | OpenSquare q p} := by
  obtain ⟨t, ht0, ht1, ha⟩ := hchart
  exact hull_owned_of_vertices q points
    (wall_ownership_sound cell points cert 0 1 hc q hcell hcont t ht0 ht1 ha
      (by simpa using ht0) (by simpa using ht1))

end
end ElevenSquare.Tasks.T02
