import ElevenSquare.Tasks.T03.SimplePolygonFan
import ElevenSquare.Tasks.T03.HomogeneousPoints

namespace ElevenSquare.Pending.T03
noncomputable section

/-- An integer numerator for the oriented area. Positive denominators preserve
its sign, so the concrete orientation check needs no rational arithmetic. -/
def HomPoint.fanCross (a b c : HomPoint) : ℤ :=
  a.x * (b.y * c.denominator - c.y * b.denominator) -
  a.y * (b.x * c.denominator - c.x * b.denominator) +
  a.denominator * (b.x * c.y - b.y * c.x)

def HomPoint.fanCrossCheck (a b c : HomPoint) : Bool :=
  decide (0 < a.denominator ∧ 0 < b.denominator ∧ 0 < c.denominator ∧
    0 < a.fanCross b c)

theorem HomPoint.fanCross_identity (a b c : HomPoint)
    (ha : 0 < a.denominator) (hb : 0 < b.denominator) (hc : 0 < c.denominator) :
    rationalCross a.point b.point c.point *
      ((a.denominator : ℚ) * b.denominator * c.denominator) = a.fanCross b c := by
  have ha' : (a.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hb' : (b.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hc' : (c.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  dsimp [rationalCross, HomPoint.point, HomPoint.fanCross]
  push_cast
  field_simp [ha', hb', hc']
  <;> ring

theorem HomPoint.fanCrossCheck_sound (a b c : HomPoint)
    (h : a.fanCrossCheck b c = true) : 0 < rationalCross a.point b.point c.point := by
  obtain ⟨ha, hb, hc, hn⟩ := of_decide_eq_true h
  have hd : (0 : ℚ) < (a.denominator : ℚ) * b.denominator * c.denominator :=
    mul_pos (mul_pos (by exact_mod_cast ha) (by exact_mod_cast hb)) (by exact_mod_cast hc)
  have hn' : (0 : ℚ) < (a.fanCross b c : ℚ) := by exact_mod_cast hn
  apply (mul_pos_iff_of_pos_right hd).mp
  rwa [a.fanCross_identity b c ha hb hc]

/-- The original edge factor is retained. Only its concrete equations are
checked after clearing positive denominators. -/
structure HomEdgeCertificate where
  numerator : ℤ
  denominator : ℕ

def HomEdgeCertificate.check (w : HomEdgeCertificate) (e : EdgePlane)
    (a b : HomPoint) : Bool :=
  decide (0 < a.denominator ∧ 0 < b.denominator ∧ 0 < w.denominator ∧ 0 < w.numerator ∧
    e.factor = (w.numerator : ℚ) / w.denominator ∧
    e.plane.a * w.denominator * a.denominator * b.denominator =
      w.numerator * (b.y * a.denominator - a.y * b.denominator) ∧
    e.plane.b * w.denominator * a.denominator * b.denominator =
      w.numerator * (a.x * b.denominator - b.x * a.denominator) ∧
    e.plane.c * w.denominator * a.denominator * b.denominator =
      w.numerator * (b.y * a.x - b.x * a.y))

theorem HomEdgeCertificate.check_sound (w : HomEdgeCertificate) (e : EdgePlane)
    (a b : HomPoint) (h : w.check e a b = true) : e.check a.point b.point = true := by
  obtain ⟨ha, hb, hw, hn, hf, hA, hB, hC⟩ := of_decide_eq_true h
  have ha' : (a.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hb' : (b.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hw' : (w.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hden : (w.denominator : ℚ) * ((a.denominator : ℚ) * b.denominator) ≠ 0 :=
    mul_ne_zero hw' (mul_ne_zero ha' hb')
  have hA' : (e.plane.a : ℚ) * w.denominator * a.denominator * b.denominator =
      (w.numerator : ℚ) * ((b.y : ℚ) * a.denominator - (a.y : ℚ) * b.denominator) := by
    exact_mod_cast hA
  have hB' : (e.plane.b : ℚ) * w.denominator * a.denominator * b.denominator =
      (w.numerator : ℚ) * ((a.x : ℚ) * b.denominator - (b.x : ℚ) * a.denominator) := by
    exact_mod_cast hB
  have hC' : (e.plane.c : ℚ) * w.denominator * a.denominator * b.denominator =
      (w.numerator : ℚ) * ((b.y : ℚ) * a.x - (b.x : ℚ) * a.y) := by
    exact_mod_cast hC
  have hAy : b.point.2 - a.point.2 =
      ((b.y : ℚ) * a.denominator - (a.y : ℚ) * b.denominator) /
        ((a.denominator : ℚ) * b.denominator) := by
    dsimp [HomPoint.point]
    field_simp [ha', hb']
    <;> ring
  have hBx : a.point.1 - b.point.1 =
      ((a.x : ℚ) * b.denominator - (b.x : ℚ) * a.denominator) /
        ((a.denominator : ℚ) * b.denominator) := by
    dsimp [HomPoint.point]
    field_simp [ha', hb']
    <;> ring
  have hCxy : (b.point.2 - a.point.2) * a.point.1 + (a.point.1 - b.point.1) * a.point.2 =
      ((b.y : ℚ) * a.x - (b.x : ℚ) * a.y) /
        ((a.denominator : ℚ) * b.denominator) := by
    dsimp [HomPoint.point]
    field_simp [ha', hb']
    <;> ring
  apply decide_eq_true
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact div_pos (by exact_mod_cast hn) (by exact_mod_cast hw)
  · rw [hAy, hf, div_mul_div_comm]
    apply (eq_div_iff hden).mpr
    convert hA' using 1 <;> ring
  · rw [hBx, hf, div_mul_div_comm]
    apply (eq_div_iff hden).mpr
    convert hB' using 1 <;> ring
  · rw [hCxy, hf, div_mul_div_comm]
    apply (eq_div_iff hden).mpr
    convert hC' using 1 <;> ring

def homFanOrientationCheck (a b : HomPoint) : List HomPoint → Bool
  | [] => false
  | [c] => a.fanCrossCheck b c
  | c::d::vs => a.fanCrossCheck b c && homFanOrientationCheck a c (d::vs)

theorem homFanOrientationCheck_sound (a b : HomPoint) (vs : List HomPoint)
    (h : homFanOrientationCheck a b vs = true) :
    fanOrientationCheck a.point b.point (vs.map HomPoint.point) = true := by
  induction vs generalizing b with
  | nil => simp [homFanOrientationCheck] at h
  | cons c rest ih =>
    cases rest with
    | nil => exact decide_eq_true (a.fanCrossCheck_sound b c h)
    | cons d rest =>
      simp only [homFanOrientationCheck, Bool.and_eq_true] at h
      simp only [List.map, fanOrientationCheck, Bool.and_eq_true]
      exact ⟨decide_eq_true (a.fanCrossCheck_sound b c h.1), ih c h.2⟩

def homEdgeChainCheck (origin previous : HomPoint) :
    List HomPoint → List EdgePlane → List HomEdgeCertificate → Bool
  | [], [e], [w] => w.check e previous origin
  | v::vs, e::es, w::ws => w.check e previous v && homEdgeChainCheck origin v vs es ws
  | _, _, _ => false

theorem homEdgeChainCheck_sound (origin previous : HomPoint) (vs : List HomPoint)
    (es : List EdgePlane) (ws : List HomEdgeCertificate)
    (h : homEdgeChainCheck origin previous vs es ws = true) :
    edgeChainCheck origin.point previous.point (vs.map HomPoint.point) es = true := by
  induction vs generalizing previous es ws with
  | nil =>
    cases es with
    | nil => simp [homEdgeChainCheck] at h
    | cons e es =>
      cases es with
      | cons f rest => simp [homEdgeChainCheck] at h
      | nil =>
        cases ws with
        | nil => simp [homEdgeChainCheck] at h
        | cons w ws =>
          cases ws with
          | cons v rest => simp [homEdgeChainCheck] at h
          | nil => exact w.check_sound e previous origin h
  | cons v vs ih =>
    cases es with
    | nil => simp [homEdgeChainCheck] at h
    | cons e es =>
      cases ws with
      | nil => simp [homEdgeChainCheck] at h
      | cons w ws =>
        simp only [homEdgeChainCheck, Bool.and_eq_true] at h
        simp only [List.map, edgeChainCheck, Bool.and_eq_true]
        exact ⟨w.check_sound e previous v h.1, ih v es ws h.2⟩

def homogeneousPolygonFanCheck : List HomPoint → List EdgePlane → List HomEdgeCertificate → Bool
  | a::b::vs, es, ws => homFanOrientationCheck a b vs && homEdgeChainCheck a a (b::vs) es ws
  | _, _, _ => false

/-- Integer checks prove the very same original rational Boolean claim. -/
theorem homogeneousPolygonFanCheck_sound (ps : List HomPoint) (es : List EdgePlane)
    (ws : List HomEdgeCertificate) (h : homogeneousPolygonFanCheck ps es ws = true) :
    polygonFanCheck (ps.map HomPoint.point) es = true := by
  cases ps with
  | nil => simp [homogeneousPolygonFanCheck] at h
  | cons a tail =>
    cases tail with
    | nil => simp [homogeneousPolygonFanCheck] at h
    | cons b vs =>
      simp only [homogeneousPolygonFanCheck, Bool.and_eq_true] at h
      simp only [List.map, polygonFanCheck, Bool.and_eq_true]
      exact ⟨homFanOrientationCheck_sound a b vs h.1,
        homEdgeChainCheck_sound a a (b::vs) es ws h.2⟩

end
end ElevenSquare.Pending.T03
