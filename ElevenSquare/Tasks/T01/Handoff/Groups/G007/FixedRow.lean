import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedSemantic

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow
open ElevenSquare Pending
noncomputable section

/-- The three kinds of target in an adaptive fixed-core G007 window. -/
inductive Target where
  | singleton (piece : FeatureCapturePiece)
  | median (polygon : Polygon)
      (pair01 pair02 pair12 : FeatureCapturePiece)
      (toPair01 toPair02 toPair12 : List BaselineCombination)
  | blocker (point : QPoint) (piece : FeatureCapturePiece)

def Target.polygon : Target → Polygon
  | .singleton piece => piece.polygon
  | .median polygon _ _ _ _ _ _ => polygon
  | .blocker _ piece => piece.polygon

def Target.blockerPoint : Target → Option QPoint
  | .singleton _ => none
  | .median _ _ _ _ _ _ _ => none
  | .blocker point _ => some point

def Target.Check (row : PoseRow) : Target → Prop
  | .singleton piece => piece.Check [G007.point] row
  | .median polygon pair01 pair02 pair12 toPair01 toPair02 toPair12 =>
      pair01.Check [G007.site0, G007.site1] row ∧
      pair02.Check [G007.site0, G007.site2] row ∧
      pair12.Check [G007.site1, G007.site2] row ∧
      BaselinePolygonImplicationCheck polygon pair01.polygon toPair01 ∧
      BaselinePolygonImplicationCheck polygon pair02.polygon toPair02 ∧
      BaselinePolygonImplicationCheck polygon pair12.polygon toPair12
  | .blocker point piece => piece.Check [point] row

structure Certificate where
  targets : List Target
  cover : BaselineCoverCertificate

def Certificate.polygons (cert : Certificate) : List Polygon :=
  cert.targets.map Target.polygon

def Certificate.blockerPoints (cert : Certificate) : List QPoint :=
  cert.targets.filterMap Target.blockerPoint

def Certificate.Check (cert : Certificate) (row : PoseRow) : Prop :=
  cert.cover.Check row.centers cert.polygons ∧
    ∀ target ∈ cert.targets, target.Check row

theorem row_choice (cert : Certificate) (row : PoseRow)
    (hcert : cert.Check row) (q : UnitSquare) (hq : row.contains q)
    (hblocked : ∀ p ∈ cert.blockerPoints,
      ¬ OpenSquare q (realPoint p)) :
    OpenSquare q (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 q := by
  obtain ⟨polygon, hpolygon, hcenter⟩ :=
    baseline_cover_certificate_sound row.centers cert.polygons
      cert.cover hcert.1 q.center hq.1
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hpolygon
  have htargetCheck := hcert.2 target htarget
  cases target with
  | singleton piece =>
      left
      exact singleton_capture G007.point q
        (feature_capture_piece_sound [G007.point] row piece
          htargetCheck q hq hcenter)
  | median polygon pair01 pair02 pair12 toPair01 toPair02 toPair12 =>
      right
      rcases htargetCheck with ⟨h01, h02, h12, hi01, hi02, hi12⟩
      exact FixedSemantic.median_target_majority row q hq polygon
        pair01 pair02 pair12 toPair01 toPair02 toPair12
        h01 h02 h12 hi01 hi02 hi12 hcenter
  | blocker point piece =>
      have hp : point ∈ cert.blockerPoints := by
        unfold Certificate.blockerPoints
        exact List.mem_filterMap.mpr
          ⟨Target.blocker point piece, htarget, rfl⟩
      exact False.elim ((hblocked point hp)
        (singleton_capture point q
          (feature_capture_piece_sound [point] row piece
            htargetCheck q hq hcenter)))

theorem packing_row_choice (cert : Certificate) (row : PoseRow)
    (hcert : cert.Check row) (P : Packing 11 coverCap) (i : Owner)
    (hq : row.contains (P.squares i))
    (howned : ∀ p ∈ cert.blockerPoints,
      ∃ j : Owner, i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    OpenSquare (P.squares i) (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 (P.squares i) := by
  apply row_choice cert row hcert (P.squares i) hq
  intro p hp ho
  obtain ⟨j, hij, hj⟩ := howned p hp
  exact P.interior_disjoint i j hij (realPoint p) ⟨ho, hj⟩

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow.packing_row_choice
