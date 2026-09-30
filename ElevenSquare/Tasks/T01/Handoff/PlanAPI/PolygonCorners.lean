import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- Chosen adjacent vertex indices for one corner, checked with exact rationals. -/
def CornerValid (vertices : List QPoint) (polygon : Polygon)
    (vc : QPoint × (ℕ × ℕ)) : Prop :=
  vc.2.1 < vertices.length ∧ vc.2.2 < vertices.length ∧
  baselineEdge (vertices.getD vc.2.1 (0, 0)) vc.1 ∈ polygon ∧
  baselineEdge vc.1 (vertices.getD vc.2.2 (0, 0)) ∈ polygon ∧
  0 < ((vertices.getD vc.2.2 (0, 0)).1 - vc.1.1) *
        ((vertices.getD vc.2.1 (0, 0)).2 - vc.1.2) -
      ((vertices.getD vc.2.2 (0, 0)).2 - vc.1.2) *
        ((vertices.getD vc.2.1 (0, 0)).1 - vc.1.1)

instance (vertices : List QPoint) (polygon : Polygon) (vc : QPoint × (ℕ × ℕ)) :
    Decidable (CornerValid vertices polygon vc) := by
  unfold CornerValid
  infer_instance

/-- An explicit pair of adjacent vertex indices for each polygon vertex.
This avoids existential search over a large rational vertex list. -/
def PolygonCornerCheck (vertices : List QPoint) (polygon : Polygon)
    (corners : List (ℕ × ℕ)) : Prop :=
  vertices ≠ [] ∧ vertices.length = corners.length ∧
  ∀ vc ∈ vertices.zip corners, CornerValid vertices polygon vc

instance (vertices : List QPoint) (polygon : Polygon) (corners : List (ℕ × ℕ)) :
    Decidable (PolygonCornerCheck vertices polygon corners) := by
  unfold PolygonCornerCheck
  infer_instance

theorem polygon_corner_check_sound (vertices : List QPoint) (polygon : Polygon)
    (corners : List (ℕ × ℕ))
    (hc : PolygonCornerCheck vertices polygon corners) :
    BaselinePolygonCheck vertices polygon := by
  refine ⟨hc.1, ?_⟩
  have hgo : ∀ (xs : List QPoint) (cs : List (ℕ × ℕ)),
      xs.length = cs.length →
      (∀ vc ∈ xs.zip cs, CornerValid vertices polygon vc) →
      ∀ v ∈ xs, ∃ u ∈ vertices, ∃ w ∈ vertices,
        baselineEdge u v ∈ polygon ∧ baselineEdge v w ∈ polygon ∧
        0 < (w.1 - v.1) * (u.2 - v.2) - (w.2 - v.2) * (u.1 - v.1) := by
    intro xs
    induction xs with
    | nil => intro cs _ _ v hv; simp at hv
    | cons v vs ih =>
      intro cs hlen hvalid p hp
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
        rcases List.mem_cons.mp hp with rfl | hp
        · have hv := hvalid (p,c) (by simp)
          have hu : vertices.getD c.1 (0,0) ∈ vertices := by
            rw [List.getD_eq_getElem vertices (0,0) hv.1]
            exact List.get_mem ..
          have hw : vertices.getD c.2 (0,0) ∈ vertices := by
            rw [List.getD_eq_getElem vertices (0,0) hv.2.1]
            exact List.get_mem ..
          exact ⟨_, hu, _, hw, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩
        · apply ih cs (by simpa using hlen)
            (fun vc hvc => hvalid vc (by simp [hvc])) p hp
  exact hgo vertices corners hc.2.1 hc.2.2

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.polygon_corner_check_sound
