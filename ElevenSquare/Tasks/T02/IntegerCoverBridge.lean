import ElevenSquare.Tasks.T02.IntegerCover
import Mathlib.Tactic.Ring

namespace ElevenSquare.Tasks.T02.IntegerCover
open ElevenSquare.Pending
noncomputable section

/-- `num * rationalPlane = den * plane`, with both factors positive.
The integer plane can therefore be primitive without requiring a fractional
scaling operation in the integer coverage checker. -/
structure NormalizedPlane where
  plane : Plane
  num : ℕ
  den : ℕ

def NormalizedPlane.Check (h : Halfplane) (z : NormalizedPlane) : Prop :=
  0 < z.num ∧ 0 < z.den ∧
  (z.num : ℚ) * h.a = z.den * (z.plane.a : ℚ) ∧
  (z.num : ℚ) * h.b = z.den * (z.plane.b : ℚ) ∧
  (z.num : ℚ) * h.c = z.den * (z.plane.c : ℚ)

instance (h : Halfplane) (z : NormalizedPlane) : Decidable (z.Check h) := by
  unfold NormalizedPlane.Check
  infer_instance

theorem normalization_sound (h : Halfplane) (z : NormalizedPlane)
    (hc : z.Check h) (p : Point) : h.contains p ↔ z.plane.contains p := by
  have hn : (0 : ℝ) < z.num := by exact_mod_cast hc.1
  have hd : (0 : ℝ) < z.den := by exact_mod_cast hc.2.1
  have ha : (z.num : ℝ) * h.a = (z.den : ℝ) * z.plane.a := by
    exact_mod_cast hc.2.2.1
  have hb : (z.num : ℝ) * h.b = (z.den : ℝ) * z.plane.b := by
    exact_mod_cast hc.2.2.2.1
  have he : (z.num : ℝ) * h.c = (z.den : ℝ) * z.plane.c := by
    exact_mod_cast hc.2.2.2.2
  have hid : (z.num : ℝ) * ((h.a : ℝ) * p.1 + (h.b : ℝ) * p.2 - h.c) =
      (z.den : ℝ) * ((z.plane.a : ℝ) * p.1 + (z.plane.b : ℝ) * p.2 - z.plane.c) := by
    calc
      _ = ((z.num : ℝ) * h.a) * p.1 + ((z.num : ℝ) * h.b) * p.2 - z.num * (h.c : ℝ) := by ring
      _ = _ := by rw [ha, hb, he]; ring
  dsimp [Halfplane.contains, Plane.contains]
  constructor <;> intro hle
  · have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hn) (sub_nonpos.mpr hle)
    rw [hid] at this
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) (sub_nonpos.mpr hle)
    rw [← hid] at this
    nlinarith

abbrev NormalizedPoly := List NormalizedPlane
def NormalizedPoly.poly (zs : NormalizedPoly) : Poly := zs.map NormalizedPlane.plane

def PolygonNormalizationCheck (hs : Polygon) (zs : NormalizedPoly) : Prop :=
  hs.length = zs.length ∧ ∀ hz ∈ hs.zip zs, hz.2.Check hz.1

instance (hs : Polygon) (zs : NormalizedPoly) :
    Decidable (PolygonNormalizationCheck hs zs) := by
  unfold PolygonNormalizationCheck
  infer_instance

theorem polygon_normalization_sound (hs : Polygon) (zs : NormalizedPoly)
    (hc : PolygonNormalizationCheck hs zs) : hs.carrier = zs.poly.carrier := by
  induction hs generalizing zs with
  | nil =>
    have hz : zs = [] := by simpa using hc.1.symm
    subst zs
    ext p
    simp [Polygon.carrier, NormalizedPoly.poly, Poly.carrier]
  | cons h hs ih =>
    cases zs with
    | nil => simp [PolygonNormalizationCheck] at hc
    | cons z zs =>
      have hhead : z.Check h := hc.2 (h, z) (by simp)
      have htail : PolygonNormalizationCheck hs zs := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro e he
        exact hc.2 e (by simp [he])
      ext p
      have heq := Set.ext_iff.mp (ih zs htail) p
      simpa only [Polygon.carrier, Poly.carrier, Set.mem_setOf_eq,
        NormalizedPoly.poly, List.map_cons, List.mem_cons, forall_eq_or_imp]
        using and_congr (normalization_sound h z hhead p) heq

def TargetsNormalizationCheck (targets : List Polygon) (zs : List NormalizedPoly) : Prop :=
  targets.length = zs.length ∧
  ∀ hz ∈ targets.zip zs, PolygonNormalizationCheck hz.1 hz.2

instance (targets : List Polygon) (zs : List NormalizedPoly) :
    Decidable (TargetsNormalizationCheck targets zs) := by
  unfold TargetsNormalizationCheck
  infer_instance

theorem targets_normalization_sound (targets : List Polygon) (zs : List NormalizedPoly)
    (hc : TargetsNormalizationCheck targets zs) :
    ∀ z ∈ zs, ∃ t ∈ targets, t.carrier = z.poly.carrier := by
  induction targets generalizing zs with
  | nil =>
    have hz : zs = [] := by simpa using hc.1.symm
    subst zs
    simp
  | cons h hs ih =>
    cases zs with
    | nil => simp
    | cons z zs =>
      have hhead : PolygonNormalizationCheck h z := hc.2 (h, z) (by simp)
      have htail : TargetsNormalizationCheck hs zs := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro e he
        exact hc.2 e (by simp [he])
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨h, by simp, polygon_normalization_sound h _ hhead⟩
      · obtain ⟨t, ht, he⟩ := ih zs htail w hw
        exact ⟨t, List.mem_cons_of_mem h ht, he⟩

structure RationalCertificate where
  source : NormalizedPoly
  targets : List NormalizedPoly
  cover : Certificate

def RationalCertificate.Check (source : Polygon) (targets : List Polygon)
    (c : RationalCertificate) : Prop :=
  PolygonNormalizationCheck source c.source ∧ TargetsNormalizationCheck targets c.targets ∧
  c.cover.Check c.source.poly (c.targets.map NormalizedPoly.poly)

instance (source : Polygon) (targets : List Polygon) (c : RationalCertificate) :
    Decidable (c.Check source targets) := by
  unfold RationalCertificate.Check
  infer_instance

/-- A checked integer cover proves coverage for the unchanged rational polygons. -/
theorem rational_certificate_sound (source : Polygon) (targets : List Polygon)
    (c : RationalCertificate) (hc : c.Check source targets)
    (p : Point) (hp : p ∈ source.carrier) : ∃ t ∈ targets, p ∈ t.carrier := by
  rw [polygon_normalization_sound source c.source hc.1] at hp
  obtain ⟨t, ht, hpt⟩ := certificate_sound _ _ c.cover hc.2.2 p hp
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ht
  obtain ⟨q, hq, he⟩ := targets_normalization_sound targets c.targets hc.2.1 z hz
  exact ⟨q, hq, he.symm ▸ hpt⟩

end
end ElevenSquare.Tasks.T02.IntegerCover
