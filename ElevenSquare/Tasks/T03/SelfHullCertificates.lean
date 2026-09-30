import ElevenSquare.Tasks.T03.Quadratic
import ElevenSquare.Tasks.T03.Promotion
import ElevenSquare.Tasks.T03.LinearCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def quadraticNonnegativeCheck (A B C lo hi : ℚ) : Bool :=
  decide (lo < hi ∧ 0 ≤ A*lo^2+B*lo+C ∧
    0 ≤ 2*(A*lo^2+B*lo+C)+(hi-lo)*(2*A*lo+B) ∧ 0 ≤ A*hi^2+B*hi+C)

theorem quadraticNonnegativeCheck_sound (A B C lo hi : ℚ)
    (h : quadraticNonnegativeCheck A B C lo hi = true) (t : ℝ)
    (ht0 : (lo:ℝ) ≤ t) (ht1 : t ≤ (hi:ℝ)) :
    0 ≤ (A:ℝ)*t^2+(B:ℝ)*t+(C:ℝ) := by
  obtain ⟨hlt,ha,hm,hb⟩ := of_decide_eq_true h
  apply quadratic_lower_bound (A:ℝ) (B:ℝ) (C:ℝ) lo hi 0 t
  · exact_mod_cast hlt
  · exact ht0
  · exact ht1
  · simpa using (show (0:ℝ) ≤ (A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ) by exact_mod_cast ha)
  · simpa using (show (0:ℝ) ≤ 2*((A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ))+
        ((hi:ℝ)-(lo:ℝ))*(2*(A:ℝ)*lo+(B:ℝ)) by exact_mod_cast hm)
  · simpa using (show (0:ℝ) ≤ (A:ℝ)*(hi:ℝ)^2+(B:ℝ)*hi+(C:ℝ) by exact_mod_cast hb)

theorem projectionRadius_of_four_bounds (q : UnitSquare) (n : Point) (E : ℝ)
    (hpp : dot q.axis n + dot (perp q.axis) n ≤ 2*E)
    (hpm : dot q.axis n - dot (perp q.axis) n ≤ 2*E)
    (hmp : -dot q.axis n + dot (perp q.axis) n ≤ 2*E)
    (hmm : -dot q.axis n - dot (perp q.axis) n ≤ 2*E) : projectionRadius q n ≤ E := by
  dsimp [projectionRadius]
  rcases le_total 0 (dot q.axis n) with hx | hx
  · rw [abs_of_nonneg hx]
    rcases le_total 0 (dot (perp q.axis) n) with hy | hy
    · rw [abs_of_nonneg hy]; linarith
    · rw [abs_of_nonpos hy]; linarith
  · rw [abs_of_nonpos hx]
    rcases le_total 0 (dot (perp q.axis) n) with hy | hy
    · rw [abs_of_nonneg hy]; linarith
    · rw [abs_of_nonpos hy]; linarith

theorem chart_signed_projection_bound (q : UnitSquare) (n : Point) (E t sx sy : ℝ)
    (hq : q.axis = chartAxis t)
    (h : 0 ≤ (2*E+sx*n.1+sy*n.2)*t^2+(-2*sx*n.2+2*sy*n.1)*t+
      (2*E-sx*n.1-sy*n.2)) :
    sx*dot q.axis n+sy*dot (perp q.axis) n ≤ 2*E := by
  have hd : 0 < 1+t^2 := by positivity
  have he : sx*dot q.axis n+sy*dot (perp q.axis) n =
      ((sx*n.1+sy*n.2)*(1-t^2)+(2*sx*n.2-2*sy*n.1)*t)/(1+t^2) := by
    rw [hq]
    dsimp [dot,perp,chartAxis]
    field_simp [ne_of_gt hd]
    ring
  rw [he]
  apply (div_le_iff hd).mpr
  nlinarith only [h]

structure RadiusCertificate where
  normal : QPoint
  bound : ℚ
  lo : ℚ
  hi : ℚ

def RadiusCertificate.signedCheck (w : RadiusCertificate) (sx sy : ℚ) : Bool :=
  quadraticNonnegativeCheck (2*w.bound+sx*w.normal.1+sy*w.normal.2)
    (-2*sx*w.normal.2+2*sy*w.normal.1) (2*w.bound-sx*w.normal.1-sy*w.normal.2) w.lo w.hi

def RadiusCertificate.check (w : RadiusCertificate) : Bool :=
  w.signedCheck 1 1 && w.signedCheck 1 (-1) && w.signedCheck (-1) 1 && w.signedCheck (-1) (-1)

theorem RadiusCertificate.signedSound (w : RadiusCertificate) (sx sy : ℚ)
    (h : w.signedCheck sx sy = true) (q : UnitSquare) (t : ℝ)
    (hq : q.axis = chartAxis t) (ht0 : (w.lo:ℝ) ≤ t) (ht1 : t ≤ (w.hi:ℝ)) :
    (sx:ℝ)*dot q.axis (realPoint w.normal)+(sy:ℝ)*dot (perp q.axis) (realPoint w.normal) ≤
      2*(w.bound:ℝ) := by
  apply chart_signed_projection_bound q (realPoint w.normal) (w.bound:ℝ) t sx sy hq
  have hh := quadraticNonnegativeCheck_sound _ _ _ _ _ h t ht0 ht1
  simpa [realPoint] using hh

theorem RadiusCertificate.sound (w : RadiusCertificate) (h : w.check = true)
    (q : UnitSquare) (t : ℝ) (hq : q.axis = chartAxis t)
    (ht0 : (w.lo:ℝ) ≤ t) (ht1 : t ≤ (w.hi:ℝ)) :
    projectionRadius q (realPoint w.normal) ≤ (w.bound:ℝ) := by
  simp only [RadiusCertificate.check,Bool.and_eq_true] at h
  apply projectionRadius_of_four_bounds
  · simpa using w.signedSound 1 1 h.1.1.1 q t hq ht0 ht1
  · simpa using w.signedSound 1 (-1) h.1.1.2 q t hq ht0 ht1
  · simpa using w.signedSound (-1) 1 h.1.2 q t hq ht0 ht1
  · simpa using w.signedSound (-1) (-1) h.2 q t hq ht0 ht1

structure SelfHullCutCertificate where
  radius : RadiusCertificate
  vertex : QPoint
  plane : IntegerPlane
  factor : ℚ

def SelfHullCutCertificate.check (w : SelfHullCutCertificate) (vs : List QPoint) : Bool :=
  decide (w.radius.check = true ∧ w.vertex ∈ vs ∧ 0 < w.factor ∧
    (w.plane.a:ℚ) = w.factor*w.radius.normal.1 ∧
    (w.plane.b:ℚ) = w.factor*w.radius.normal.2 ∧
    (w.plane.c:ℚ) = w.factor*(w.vertex.1*w.radius.normal.1+
      w.vertex.2*w.radius.normal.2+w.radius.bound))

theorem SelfHullCutCertificate.sound (w : SelfHullCutCertificate) (vs : List QPoint)
    (h : w.check vs = true) (q : UnitSquare) (t : ℝ)
    (hold : rationalHull vs ⊆ {p | OpenSquare q p}) (hq : q.axis = chartAxis t)
    (ht0 : (w.radius.lo:ℝ) ≤ t) (ht1 : t ≤ (w.radius.hi:ℝ)) : w.plane.holds q.center := by
  obtain ⟨hr,hv,hf,ha,hb,hc⟩ := of_decide_eq_true h
  have hbnd := selfHull_center_upper q vs hold w.vertex hv (realPoint w.radius.normal)
    (w.radius.bound:ℝ) (w.radius.sound hr q t hq ht0 ht1)
  have hf' : (0:ℝ) < w.factor := by exact_mod_cast hf
  have ha' : (w.plane.a:ℝ) = (w.factor:ℝ)*(w.radius.normal.1:ℝ) := by exact_mod_cast ha
  have hb' : (w.plane.b:ℝ) = (w.factor:ℝ)*(w.radius.normal.2:ℝ) := by exact_mod_cast hb
  have hc' : (w.plane.c:ℝ) = (w.factor:ℝ)*((w.vertex.1:ℝ)*(w.radius.normal.1:ℝ)+
      (w.vertex.2:ℝ)*(w.radius.normal.2:ℝ)+(w.radius.bound:ℝ)) := by exact_mod_cast hc
  dsimp [IntegerPlane.holds]
  rw [ha',hb',hc']
  have hmul := mul_le_mul_of_nonneg_left hbnd hf'.le
  dsimp [dot,realPoint] at hmul
  nlinarith only [hmul]

end
end ElevenSquare.Pending.T03
