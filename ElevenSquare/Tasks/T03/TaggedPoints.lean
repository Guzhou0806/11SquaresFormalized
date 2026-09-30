import ElevenSquare.Tasks.T03.CorePointCertificates
import ElevenSquare.Tasks.T03.Promotion

namespace ElevenSquare.Pending.T03
noncomputable section

inductive TaggedPointCertificate where
  | oldVertex
  | oldHull (witness : Barycentric3)
  | core (witnesses : List Barycentric3)
  | mix (oldPoint corePoint : QPoint) (weight : ℚ)
      (oldWitness : Barycentric3) (coreWitnesses : List Barycentric3)

def TaggedPointCertificate.check (old core centers : List QPoint) (p : QPoint) :
    TaggedPointCertificate → Bool
  | .oldVertex => decide (p ∈ old)
  | .oldHull w => w.check old p
  | .core ws => corePointCheck core p centers ws
  | .mix a b w wa wb => decide (0 ≤ w ∧ w ≤ 1 ∧
      wa.check old a = true ∧ corePointCheck core b centers wb = true ∧
      p.1=(1-w)*a.1+w*b.1 ∧ p.2=(1-w)*a.2+w*b.2)

theorem TaggedPointCertificate.sound (old core centers : List QPoint) (p : QPoint)
    (w : TaggedPointCertificate) (h : w.check old core centers p = true)
    (q : UnitSquare) (hold : rationalHull old ⊆ {p | OpenSquare q p})
    (hcore : CoreFits (rationalHull core) q) (hc : q.center ∈ rationalHull centers) :
    OpenSquare q (realPoint p) := by
  cases w with
  | oldVertex => exact hold (subset_convexHull ℝ _ ⟨p,of_decide_eq_true h,rfl⟩)
  | oldHull w => exact hold (w.mem_hull old p h)
  | core ws => exact corePointCheck_owned core p centers ws h q hcore hc
  | mix a b weight wa wb =>
    obtain ⟨h0,h1,ha,hb,hx,hy⟩ := of_decide_eq_true h
    have h0' : (0:ℝ) ≤ weight := by exact_mod_cast h0
    have h1' : (weight:ℝ) ≤ 1 := by exact_mod_cast h1
    have he : realPoint p = (1-(weight:ℝ)) • realPoint a+(weight:ℝ) • realPoint b := by
      ext <;> dsimp [realPoint]
      · exact_mod_cast hx
      · exact_mod_cast hy
    rw [he]
    exact openSquare_convex q (hold (wa.mem_hull old a ha))
      (corePointCheck_owned core b centers wb hb q hcore hc)
      (sub_nonneg.mpr h1') h0' (sub_add_cancel 1 _)

def taggedPointsCheck (old core centers : List QPoint) :
    List QPoint → List TaggedPointCertificate → Bool
  | [], [] => true
  | p::ps, w::ws => w.check old core centers p && taggedPointsCheck old core centers ps ws
  | _, _ => false

theorem taggedPointsCheck_sound (old core centers chosen : List QPoint)
    (ws : List TaggedPointCertificate) (h : taggedPointsCheck old core centers chosen ws = true)
    (q : UnitSquare) (hold : rationalHull old ⊆ {p | OpenSquare q p})
    (hcore : CoreFits (rationalHull core) q) (hc : q.center ∈ rationalHull centers) :
    ∀ p ∈ chosen, OpenSquare q (realPoint p) := by
  induction chosen generalizing ws with
  | nil => simp
  | cons p ps ih =>
    cases ws with
    | nil => simp [taggedPointsCheck] at h
    | cons w ws =>
      simp only [taggedPointsCheck,Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact w.sound old core centers v h.1 q hold hcore hc
      · exact ih ws h.2 v hv

end
end ElevenSquare.Pending.T03
