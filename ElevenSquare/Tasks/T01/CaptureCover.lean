import ElevenSquare.Tasks.T01.FiniteMajority

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Each region captures its listed feature. A singleton feature can later be
excluded using an independently owned point of a distinct packing square. -/
abbrev CaptureCoverPlan := List (List QPoint × FeatureCapturePiece)

def CaptureCoverCheck (r : PoseRow) (plan : CaptureCoverPlan)
    (cover : BaselineCoverCertificate) : Prop :=
  cover.Check r.centers (plan.map (fun x => x.2.polygon)) ∧
    ∀ item ∈ plan, item.2.Check item.1 r

theorem checked_capture_cover (r : PoseRow) (plan : CaptureCoverPlan)
    (cover : BaselineCoverCertificate) (hc : CaptureCoverCheck r plan cover)
    (q : UnitSquare) (hq : r.contains q) :
    ∃ item ∈ plan, ∃ p ∈ rationalHull item.1, OpenSquare q p := by
  obtain ⟨poly, hp, hcenter⟩ := baseline_cover_certificate_sound _ _ cover hc.1 q.center hq.1
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨item, hi, feature_capture_piece_sound item.1 r item.2 (hc.2 item hi) q hq hcenter⟩

theorem singleton_capture (p : QPoint) (q : UnitSquare)
    (h : ∃ x ∈ rationalHull [p], OpenSquare q x) : OpenSquare q (realPoint p) := by
  obtain ⟨x, hx, ho⟩ := h
  have he : {x : Point | ∃ v ∈ ([p] : List QPoint), x = realPoint v} = {realPoint p} := by
    ext x
    simp only [List.mem_singleton, exists_eq_left, Set.mem_setOf_eq, Set.mem_singleton_iff]
  change x ∈ convexHull ℝ {x : Point | ∃ v ∈ ([p] : List QPoint), x = realPoint v} at hx
  rw [he, convexHull_singleton] at hx
  exact (Set.mem_singleton_iff.mp hx) ▸ ho

end
end ElevenSquare.Tasks.T01
