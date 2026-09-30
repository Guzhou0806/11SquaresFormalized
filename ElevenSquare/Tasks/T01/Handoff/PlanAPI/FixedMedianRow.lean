import ElevenSquare.Tasks.T01.CaptureCover
import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedMedianRow
open ElevenSquare.Pending
noncomputable section

/-- A constant polygon cover consists of one majority target and point blockers. -/
theorem row_majority (sites : Finset QPoint) (k : ℕ)
    (row : PoseRow) (medianTarget : Polygon)
    (blockers : List (QPoint × FeatureCapturePiece))
    (cover : BaselineCoverCertificate)
    (hcover : cover.Check row.centers
      (medianTarget :: blockers.map (fun b => b.2.polygon)))
    (hmedian : ∀ q : UnitSquare, row.contains q → q.center ∈ medianTarget.carrier →
      BaselineMajorityCapture sites k q)
    (hpieces : ∀ b ∈ blockers, b.2.Check [b.1] row)
    (q : UnitSquare) (hq : row.contains q)
    (hblocked : ∀ b ∈ blockers, ¬ OpenSquare q (realPoint b.1)) :
    BaselineMajorityCapture sites k q := by
  obtain ⟨target, htarget, hcenter⟩ := baseline_cover_certificate_sound
    row.centers (medianTarget :: blockers.map (fun b => b.2.polygon))
    cover hcover q.center hq.1
  rcases List.mem_cons.mp htarget with rfl | htarget
  · exact hmedian q hq hcenter
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp htarget
    exact False.elim (hblocked b hb (singleton_capture b.1 q
      (feature_capture_piece_sound [b.1] row b.2 (hpieces b hb) q hq hcenter)))

theorem packing_majority (sites : Finset QPoint) (k : ℕ)
    (row : PoseRow) (medianTarget : Polygon)
    (blockers : List (QPoint × FeatureCapturePiece))
    (cover : BaselineCoverCertificate)
    (hcover : cover.Check row.centers
      (medianTarget :: blockers.map (fun b => b.2.polygon)))
    (hmedian : ∀ q : UnitSquare, row.contains q → q.center ∈ medianTarget.carrier →
      BaselineMajorityCapture sites k q)
    (hpieces : ∀ b ∈ blockers, b.2.Check [b.1] row)
    (P : Packing 11 coverCap) (i : Owner) (hq : row.contains (P.squares i))
    (howned : ∀ b ∈ blockers, ∃ j : Owner,
      i ≠ j ∧ OpenSquare (P.squares j) (realPoint b.1)) :
    BaselineMajorityCapture sites k (P.squares i) := by
  apply row_majority sites k row medianTarget blockers cover
    hcover hmedian hpieces (P.squares i) hq
  intro b hb hinside
  obtain ⟨j, hij, hj⟩ := howned b hb
  exact P.interior_disjoint i j hij (realPoint b.1) ⟨hinside, hj⟩

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedMedianRow

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedMedianRow.packing_majority
