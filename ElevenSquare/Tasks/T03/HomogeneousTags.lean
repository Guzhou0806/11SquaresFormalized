import ElevenSquare.Tasks.T03.HomogeneousPoints
import ElevenSquare.Tasks.T03.PlaneTaggedPoints

namespace ElevenSquare.Pending.T03
noncomputable section

def homCorePointCheck (ls : List IntegerPlane) (p : HomPoint) (cs : List HomPoint) : Bool :=
  decide (0 < p.denominator) && cs.all (fun c =>
    decide (0 < c.denominator) && ls.all (fun l => (p.sub c).planeCheck l))

theorem homCorePointCheck_owned (core : List QPoint) (ls : List IntegerPlane)
    (p : HomPoint) (cs : List HomPoint) (h : homCorePointCheck ls p cs = true)
    (hpoly : IntegerCarrier ls ⊆ rationalHull core) (q : UnitSquare)
    (hfit : CoreFits (rationalHull core) q)
    (hc : q.center ∈ rationalHull (cs.map HomPoint.point)) :
    OpenSquare q (realPoint p.point) := by
  simp only [homCorePointCheck,Bool.and_eq_true,List.all_eq_true] at h
  apply owned_of_hull_core q (cs.map HomPoint.point) (rationalHull core) (realPoint p.point)
    (convex_convexHull ℝ _) hfit hc
  intro c hc'
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc'
  apply hpoly
  intro l hl
  have hh := (p.sub x).planeCheck_sound l ((h.2 x hx).2 l hl)
  rw [HomPoint.sub_point p x (of_decide_eq_true h.1)
    (of_decide_eq_true (h.2 x hx).1)] at hh
  simpa [realPoint] using hh

inductive HomPointTag where
  | oldVertex
  | oldHull (witness : Barycentric3)
  | core (point : HomPoint)
  | mix (oldPoint : QPoint) (corePoint : HomPoint) (weight : ℚ) (oldWitness : Barycentric3)

def HomPointTag.check (old : List QPoint) (ls : List IntegerPlane)
    (cs : List HomPoint) (p : QPoint) : HomPointTag → Bool
  | .oldVertex => decide (p ∈ old)
  | .oldHull w => w.check old p
  | .core x => decide (p=x.point) && homCorePointCheck ls x cs
  | .mix a b weight wa => decide (0 ≤ weight ∧ weight ≤ 1 ∧
      wa.check old a = true ∧
      p.1=(1-weight)*a.1+weight*b.point.1 ∧ p.2=(1-weight)*a.2+weight*b.point.2) &&
      homCorePointCheck ls b cs

theorem HomPointTag.sound (old core : List QPoint) (ls : List IntegerPlane)
    (cs : List HomPoint) (p : QPoint) (w : HomPointTag)
    (h : w.check old ls cs p = true) (hpoly : IntegerCarrier ls ⊆ rationalHull core)
    (q : UnitSquare) (hold : rationalHull old ⊆ {p | OpenSquare q p})
    (hfit : CoreFits (rationalHull core) q) (hc : q.center ∈ rationalHull (cs.map HomPoint.point)) :
    OpenSquare q (realPoint p) := by
  cases w with
  | oldVertex => exact hold (subset_convexHull ℝ _ ⟨p,of_decide_eq_true h,rfl⟩)
  | oldHull w => exact hold (w.mem_hull old p h)
  | core x =>
    simp only [check,Bool.and_eq_true] at h
    rw [of_decide_eq_true h.1]
    exact homCorePointCheck_owned core ls x cs h.2 hpoly q hfit hc
  | mix a b weight wa =>
    simp only [check,Bool.and_eq_true] at h
    obtain ⟨h0,h1,ha,hx,hy⟩ := of_decide_eq_true h.1
    have h0' : (0:ℝ) ≤ weight := by exact_mod_cast h0
    have h1' : (weight:ℝ) ≤ 1 := by exact_mod_cast h1
    have he : realPoint p = (1-(weight:ℝ)) • realPoint a+(weight:ℝ) • realPoint b.point := by
      ext <;> dsimp [realPoint]
      · exact_mod_cast hx
      · exact_mod_cast hy
    rw [he]
    exact openSquare_convex q (hold (wa.mem_hull old a ha))
      (homCorePointCheck_owned core ls b cs h.2 hpoly q hfit hc)
      (sub_nonneg.mpr h1') h0' (sub_add_cancel 1 _)

def homTaggedPointsCheck (old : List QPoint) (ls : List IntegerPlane)
    (cs : List HomPoint) : List QPoint → List HomPointTag → Bool
  | [], [] => true
  | p::ps,w::ws => w.check old ls cs p && homTaggedPointsCheck old ls cs ps ws
  | _, _ => false

theorem homTaggedPointsCheck_sound (old core : List QPoint) (ls : List IntegerPlane)
    (cs : List HomPoint) (chosen : List QPoint) (ws : List HomPointTag)
    (h : homTaggedPointsCheck old ls cs chosen ws = true)
    (hpoly : IntegerCarrier ls ⊆ rationalHull core) (q : UnitSquare)
    (hold : rationalHull old ⊆ {p | OpenSquare q p})
    (hfit : CoreFits (rationalHull core) q) (hc : q.center ∈ rationalHull (cs.map HomPoint.point)) :
    ∀ p ∈ chosen, OpenSquare q (realPoint p) := by
  induction chosen generalizing ws with
  | nil => simp
  | cons p ps ih =>
    cases ws with
    | nil => simp [homTaggedPointsCheck] at h
    | cons w ws =>
      simp only [homTaggedPointsCheck,Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact w.sound old core ls cs v h.1 hpoly q hold hfit hc
      · exact ih ws h.2 v hv

end
end ElevenSquare.Pending.T03
