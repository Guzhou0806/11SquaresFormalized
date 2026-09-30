import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- Explicit adjacent vertices and incident halfplanes replace an existential
search over all vertex pairs. All four indices and both edge identities are
checked; the producer's claimed ordering is not trusted. -/
structure PolygonCorner where
  before : ℕ
  after : ℕ
  incoming : ℕ
  outgoing : ℕ

def PolygonCorner.Check (vs : List QPoint) (hs : Polygon) (v : QPoint)
    (w : PolygonCorner) : Prop :=
  w.before < vs.length ∧ w.after < vs.length ∧
  w.incoming < hs.length ∧ w.outgoing < hs.length ∧
  baselineEdge (vs.getD w.before (0,0)) v = hs.getD w.incoming baselineZeroHalfplane ∧
  baselineEdge v (vs.getD w.after (0,0)) = hs.getD w.outgoing baselineZeroHalfplane ∧
  0 < ((vs.getD w.after (0,0)).1 - v.1) * ((vs.getD w.before (0,0)).2 - v.2) -
      ((vs.getD w.after (0,0)).2 - v.2) * ((vs.getD w.before (0,0)).1 - v.1)

instance polygonCornerCheckDecidable (vs : List QPoint) (hs : Polygon) (v : QPoint) (w : PolygonCorner) :
    Decidable (w.Check vs hs v) := by
  unfold PolygonCorner.Check
  infer_instance

def PolygonCornersCheck (vs : List QPoint) (hs : Polygon) (ws : List PolygonCorner) : Prop :=
  vs ≠ [] ∧ vs.length = ws.length ∧ ∀ vw ∈ vs.zip ws, vw.2.Check vs hs vw.1

instance polygonCornersCheckDecidable (vs : List QPoint) (hs : Polygon) (ws : List PolygonCorner) :
    Decidable (PolygonCornersCheck vs hs ws) := by
  unfold PolygonCornersCheck
  infer_instance

theorem zip_witness {α β : Type*} (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) (x : α) (hx : x ∈ xs) :
    ∃ y, (x,y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp⟩
      · obtain ⟨y, hy⟩ := ih ys (by simpa using hlen) hx
        exact ⟨y, by simp [hy]⟩

theorem polygon_corners_sound (vs : List QPoint) (hs : Polygon)
    (ws : List PolygonCorner) (hc : PolygonCornersCheck vs hs ws) :
    BaselinePolygonCheck vs hs := by
  refine ⟨hc.1, ?_⟩
  intro v hv
  obtain ⟨w, hw⟩ := zip_witness vs ws hc.2.1 v hv
  rcases hc.2.2 (v,w) hw with ⟨hb, ha, hi, ho, hin, hout, hturn⟩
  refine ⟨vs.getD w.before (0,0), ?_, vs.getD w.after (0,0), ?_, ?_, ?_, hturn⟩
  · rw [List.getD_eq_get vs (0,0) hb]
    exact List.get_mem ..
  · rw [List.getD_eq_get vs (0,0) ha]
    exact List.get_mem ..
  · rw [hin, List.getD_eq_get hs baselineZeroHalfplane hi]
    exact List.get_mem ..
  · rw [hout, List.getD_eq_get hs baselineZeroHalfplane ho]
    exact List.get_mem ..

end
end ElevenSquare.Tasks.T02

#print axioms ElevenSquare.Tasks.T02.polygon_corners_sound
