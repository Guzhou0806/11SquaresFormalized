import ElevenSquare.Tasks.T03.TaggedPoints
import ElevenSquare.Tasks.T03.HullLinearCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

theorem rationalHull_subset_of_vertex_membership (vs ws : List QPoint)
    (h : ∀ v ∈ vs, v ∈ ws) : rationalHull vs ⊆ rationalHull ws := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro p ⟨v,hv,rfl⟩
  exact subset_convexHull ℝ _ ⟨v,h v hv,rfl⟩

/-- Direct core halfplane checks replace an explicit barycentric witness for
every chosen-point/center-vertex pair. -/
def corePlanePointCheck (ls : List IntegerPlane) (p : QPoint) (centers : List QPoint) : Bool :=
  decide (∀ c ∈ centers, ∀ l ∈ ls, l.pointCheck (p-c) = true)

theorem corePlanePointCheck_owned (core : List QPoint) (ls : List IntegerPlane)
    (p : QPoint) (centers : List QPoint) (h : corePlanePointCheck ls p centers = true)
    (hpoly : IntegerCarrier ls ⊆ rationalHull core)
    (q : UnitSquare) (hfit : CoreFits (rationalHull core) q)
    (hc : q.center ∈ rationalHull centers) : OpenSquare q (realPoint p) := by
  apply owned_of_hull_core q centers (rationalHull core) (realPoint p)
    (convex_convexHull ℝ _) hfit hc
  intro c hc'
  apply hpoly
  intro l hl
  have hh := l.pointCheck_sound (p-c) ((of_decide_eq_true h) c hc' l hl)
  simpa [realPoint] using hh

inductive PlanePointTag where
  | oldVertex
  | oldHull (witness : Barycentric3)
  | core
  | mix (oldPoint corePoint : QPoint) (weight : ℚ) (oldWitness : Barycentric3)

def PlanePointTag.check (old : List QPoint) (ls : List IntegerPlane)
    (centers : List QPoint) (p : QPoint) : PlanePointTag → Bool
  | .oldVertex => decide (p ∈ old)
  | .oldHull w => w.check old p
  | .core => corePlanePointCheck ls p centers
  | .mix a b weight wa => decide (0 ≤ weight ∧ weight ≤ 1 ∧
      wa.check old a = true ∧ corePlanePointCheck ls b centers = true ∧
      p.1=(1-weight)*a.1+weight*b.1 ∧ p.2=(1-weight)*a.2+weight*b.2)

theorem PlanePointTag.sound (old core : List QPoint) (ls : List IntegerPlane)
    (centers : List QPoint) (p : QPoint) (w : PlanePointTag)
    (h : w.check old ls centers p = true) (hpoly : IntegerCarrier ls ⊆ rationalHull core)
    (q : UnitSquare) (hold : rationalHull old ⊆ {p | OpenSquare q p})
    (hfit : CoreFits (rationalHull core) q) (hc : q.center ∈ rationalHull centers) :
    OpenSquare q (realPoint p) := by
  cases w with
  | oldVertex => exact hold (subset_convexHull ℝ _ ⟨p,of_decide_eq_true h,rfl⟩)
  | oldHull w => exact hold (w.mem_hull old p h)
  | core => exact corePlanePointCheck_owned core ls p centers h hpoly q hfit hc
  | mix a b weight wa =>
    obtain ⟨h0,h1,ha,hb,hx,hy⟩ := of_decide_eq_true h
    have h0' : (0:ℝ) ≤ weight := by exact_mod_cast h0
    have h1' : (weight:ℝ) ≤ 1 := by exact_mod_cast h1
    have he : realPoint p = (1-(weight:ℝ)) • realPoint a+(weight:ℝ) • realPoint b := by
      ext <;> dsimp [realPoint]
      · exact_mod_cast hx
      · exact_mod_cast hy
    rw [he]
    exact openSquare_convex q (hold (wa.mem_hull old a ha))
      (corePlanePointCheck_owned core ls b centers hb hpoly q hfit hc)
      (sub_nonneg.mpr h1') h0' (sub_add_cancel 1 _)

def planeTaggedPointsCheck (old : List QPoint) (ls : List IntegerPlane)
    (centers : List QPoint) : List QPoint → List PlanePointTag → Bool
  | [], [] => true
  | p::ps, w::ws => w.check old ls centers p && planeTaggedPointsCheck old ls centers ps ws
  | _, _ => false

theorem planeTaggedPointsCheck_sound (old core : List QPoint) (ls : List IntegerPlane)
    (centers chosen : List QPoint) (ws : List PlanePointTag)
    (h : planeTaggedPointsCheck old ls centers chosen ws = true)
    (hpoly : IntegerCarrier ls ⊆ rationalHull core)
    (q : UnitSquare) (hold : rationalHull old ⊆ {p | OpenSquare q p})
    (hfit : CoreFits (rationalHull core) q) (hc : q.center ∈ rationalHull centers) :
    ∀ p ∈ chosen, OpenSquare q (realPoint p) := by
  induction chosen generalizing ws with
  | nil => simp
  | cons p ps ih =>
    cases ws with
    | nil => simp [planeTaggedPointsCheck] at h
    | cons w ws =>
      simp only [planeTaggedPointsCheck,Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact w.sound old core ls centers v h.1 hpoly q hold hfit hc
      · exact ih ws h.2 v hv

end
end ElevenSquare.Pending.T03
