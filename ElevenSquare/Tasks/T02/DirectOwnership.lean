import ElevenSquare.Tasks.T02.Quadratic
import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- Check only the chosen point's offsets from center-domain vertices. The
quadratic checks are strict and cover the whole closed orientation interval. -/
def DirectPointCheck (r : PoseRow) (centers : List QPoint) (p : QPoint) : Prop :=
  BaselinePolygonCheck centers r.centers ∧
  ∀ c ∈ centers, BaselineCoreVertexCheck (p.1-c.1, p.2-c.2) r.lo r.hi

instance (r : PoseRow) (centers : List QPoint) (p : QPoint) :
    Decidable (DirectPointCheck r centers p) := by
  unfold DirectPointCheck
  infer_instance

theorem directPointCheck_sound (r : PoseRow) (centers : List QPoint) (p : QPoint)
    (hc : DirectPointCheck r centers p) (q : UnitSquare) (hq : r.contains q) :
    OpenSquare q (realPoint p) := by
  obtain ⟨t, _, _, hl, hu, ha⟩ := hq.2
  let f : Point →ᵃ[ℝ] Point :=
    AffineMap.const ℝ Point (q.center + realPoint p) - AffineMap.id ℝ Point
  have hconv : Convex ℝ {c : Point | OpenSquare q (q.center + realPoint p - c)} := by
    simpa [f] using (openSquare_convex q).affine_preimage f
  have hv : {c | ∃ v ∈ centers, c = realPoint v} ⊆
      {c | OpenSquare q (q.center + realPoint p - c)} := by
    rintro c ⟨v, hmem, rfl⟩
    have ho := baseline_core_vertex_check_sound q (p.1-v.1, p.2-v.2)
      r.lo r.hi (hc.2 v hmem) t hl hu ha
    have he : q.center + realPoint (p.1-v.1, p.2-v.2) =
        q.center + realPoint p - realPoint v := by
      ext <;> simp [realPoint] <;> ring
    rw [he] at ho
    exact ho
  have hh := convexHull_min hv hconv
  have hp := hh (baseline_polygon_check_sound centers r.centers hc.1 hq.1)
  simpa using hp

/-- Promote literal chosen points from per-row finite checks, retaining the
previous hull. No full intermediate common-kernel polygon is required. -/
theorem checked_direct_promotion (s : PoseState) (i : Owner) (chosen : List QPoint)
    (centers : PoseRow → List QPoint)
    (hcheck : ∀ r ∈ s.rows i, ∀ p ∈ chosen, DirectPointCheck r (centers r) p) :
    VerifiedStep s (replaceHull s i (s.owned i ++ chosen)) := by
  apply VerifiedStep.promoteOwned
  intro q hq hold p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hold (subset_convexHull ℝ _ ⟨p, hp, rfl⟩)
  · rcases hq with ⟨r, hr, hcontains⟩
    exact directPointCheck_sound r (centers r) p (hcheck r hr p hp) q hcontains

end
end ElevenSquare.Tasks.T02
