import ElevenSquare.Tasks.T03.SelfHullCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def quadraticPositiveCheck (A B C lo hi : ℚ) : Bool :=
  decide ((lo < hi ∧ 0 < A*lo^2+B*lo+C ∧
    0 < 2*(A*lo^2+B*lo+C)+(hi-lo)*(2*A*lo+B) ∧ 0 < A*hi^2+B*hi+C) ∨
    (0 < A ∧ 0 < 4*A*C-B^2))

theorem quadraticPositiveCheck_sound (A B C lo hi : ℚ)
    (h : quadraticPositiveCheck A B C lo hi = true) (t : ℝ)
    (ht0 : (lo:ℝ) ≤ t) (ht1 : t ≤ (hi:ℝ)) :
    0 < (A:ℝ)*t^2+(B:ℝ)*t+(C:ℝ) := by
  rcases of_decide_eq_true h with ⟨hab,ha,hm,hb⟩ | ⟨ha,hd⟩
  · have hab' : (lo:ℝ) < (hi:ℝ) := by exact_mod_cast hab
    have ha' : (0:ℝ) < (A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ) := by exact_mod_cast ha
    have hm' : (0:ℝ) < 2*((A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ))+
        ((hi:ℝ)-(lo:ℝ))*(2*(A:ℝ)*lo+(B:ℝ)) := by exact_mod_cast hm
    have hb' : (0:ℝ) < (A:ℝ)*(hi:ℝ)^2+(B:ℝ)*hi+(C:ℝ) := by exact_mod_cast hb
    let e : ℝ := min ((A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ))
      (min ((A:ℝ)*(hi:ℝ)^2+(B:ℝ)*hi+(C:ℝ))
        ((2*((A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ))+
          ((hi:ℝ)-(lo:ℝ))*(2*(A:ℝ)*lo+(B:ℝ)))/2))
    have he : 0 < e := lt_min ha' (lt_min hb' (by linarith))
    have he0 := min_le_left ((A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ))
      (min ((A:ℝ)*(hi:ℝ)^2+(B:ℝ)*hi+(C:ℝ))
        ((2*((A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ))+
          ((hi:ℝ)-(lo:ℝ))*(2*(A:ℝ)*lo+(B:ℝ)))/2))
    have he1 : e ≤ (A:ℝ)*(hi:ℝ)^2+(B:ℝ)*hi+(C:ℝ) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have he2 : e ≤ (2*((A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ))+
        ((hi:ℝ)-(lo:ℝ))*(2*(A:ℝ)*lo+(B:ℝ)))/2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have he0' : e ≤ (A:ℝ)*(lo:ℝ)^2+(B:ℝ)*lo+(C:ℝ) := he0
    have hh := quadratic_lower_bound (A:ℝ) (B:ℝ) (C:ℝ) lo hi e t
      hab' ht0 ht1 (by linarith) (by linarith) (by linarith)
    exact lt_of_lt_of_le he hh
  · exact quadratic_pos_of_discriminant (A:ℝ) (B:ℝ) (C:ℝ) t
      (by exact_mod_cast ha) (by exact_mod_cast hd)

def vertexCoreCheck (v : QPoint) (lo hi : ℚ) : Bool :=
  quadraticPositiveCheck (1/2+v.1) (-2*v.2) (1/2-v.1) lo hi &&
  quadraticPositiveCheck (1/2-v.1) (2*v.2) (1/2+v.1) lo hi &&
  quadraticPositiveCheck (1/2+v.2) (2*v.1) (1/2-v.2) lo hi &&
  quadraticPositiveCheck (1/2-v.2) (-2*v.1) (1/2+v.2) lo hi

theorem vertexCoreCheck_sound (v : QPoint) (lo hi : ℚ)
    (h : vertexCoreCheck v lo hi = true) (q : UnitSquare) (t : ℝ)
    (ht0 : (lo:ℝ) ≤ t) (ht1 : t ≤ (hi:ℝ)) (hq : q.axis=chartAxis t) :
    OpenSquare q (q.center+realPoint v) := by
  simp only [vertexCoreCheck,Bool.and_eq_true] at h
  apply openSquare_of_chart_quadratics q (realPoint v) t hq
  · simpa [realPoint] using quadraticPositiveCheck_sound _ _ _ lo hi h.1.1.1 t ht0 ht1
  · simpa [realPoint] using quadraticPositiveCheck_sound _ _ _ lo hi h.1.1.2 t ht0 ht1
  · simpa [realPoint] using quadraticPositiveCheck_sound _ _ _ lo hi h.1.2 t ht0 ht1
  · simpa [realPoint] using quadraticPositiveCheck_sound _ _ _ lo hi h.2 t ht0 ht1

def strictCoreCheck (vs : List QPoint) (lo hi : ℚ) : Bool :=
  decide (∀ v ∈ vs, vertexCoreCheck v lo hi = true)

theorem strictCoreCheck_sound (vs : List QPoint) (lo hi : ℚ)
    (h : strictCoreCheck vs lo hi = true) (q : UnitSquare) (t : ℝ)
    (ht0 : (lo:ℝ) ≤ t) (ht1 : t ≤ (hi:ℝ)) (hq : q.axis=chartAxis t) :
    CoreFits (rationalHull vs) q := by
  apply common_core_hull
  intro v hv
  exact vertexCoreCheck_sound v lo hi ((of_decide_eq_true h) v hv) q t ht0 ht1 hq

end
end ElevenSquare.Pending.T03
