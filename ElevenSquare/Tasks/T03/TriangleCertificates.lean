import ElevenSquare.Tasks.T03.TriangleCover

namespace ElevenSquare.Pending.T03
noncomputable section

def rationalCross (a b p : QPoint) : ℚ :=
  (b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1)

theorem rationalCross_cast (a b p : QPoint) :
    (rationalCross a b p : ℝ) = orientedCross (realPoint a) (realPoint b) (realPoint p) := by
  simp [rationalCross, orientedCross, realPoint]

/-- A positive rational scale identifies a closed oriented edge exactly. -/
structure EdgePlane where
  plane : IntegerPlane
  factor : ℚ

def EdgePlane.check (e : EdgePlane) (a b : QPoint) : Bool :=
  decide (0 < e.factor ∧
    (e.plane.a:ℚ) = e.factor*(b.2-a.2) ∧
    (e.plane.b:ℚ) = e.factor*(a.1-b.1) ∧
    (e.plane.c:ℚ) = e.factor*((b.2-a.2)*a.1+(a.1-b.1)*a.2))

theorem EdgePlane.sound (e : EdgePlane) (a b : QPoint) (h : e.check a b = true)
    (p : Point) (hp : e.plane.holds p) :
    0 ≤ orientedCross (realPoint a) (realPoint b) p := by
  obtain ⟨hf,ha,hb,hc⟩ := of_decide_eq_true h
  have hf' : (0:ℝ) < e.factor := by exact_mod_cast hf
  have ha' : (e.plane.a:ℝ) = (e.factor:ℝ)*((b.2:ℝ)-(a.2:ℝ)) := by exact_mod_cast ha
  have hb' : (e.plane.b:ℝ) = (e.factor:ℝ)*((a.1:ℝ)-(b.1:ℝ)) := by exact_mod_cast hb
  have hc' : (e.plane.c:ℝ) = (e.factor:ℝ)*
      (((b.2:ℝ)-(a.2:ℝ))*(a.1:ℝ)+((a.1:ℝ)-(b.1:ℝ))*(a.2:ℝ)) := by
    exact_mod_cast hc
  dsimp [IntegerPlane.holds] at hp
  rw [ha',hb',hc'] at hp
  apply (mul_le_mul_left hf').mp
  dsimp [orientedCross,realPoint]
  nlinarith only [hp]

structure TriangleCertificate where
  a : QPoint
  b : QPoint
  c : QPoint
  ab : EdgePlane
  bc : EdgePlane
  ca : EdgePlane
  wab : LinearCertificate
  wbc : LinearCertificate
  wca : LinearCertificate

def TriangleCertificate.check (w : TriangleCertificate) (D : List IntegerPlane) : Bool :=
  decide (0 < rationalCross w.a w.b w.c ∧
    w.ab.check w.a w.b = true ∧ w.bc.check w.b w.c = true ∧ w.ca.check w.c w.a = true ∧
    w.wab.check D w.ab.plane = true ∧ w.wbc.check D w.bc.plane = true ∧
    w.wca.check D w.ca.plane = true)

theorem TriangleCertificate.sound (w : TriangleCertificate) (D : List IntegerPlane)
    (h : w.check D = true) (F : Set Point) (hF : Convex ℝ F)
    (ha : realPoint w.a ∈ F) (hb : realPoint w.b ∈ F) (hc : realPoint w.c ∈ F) :
    IntegerCarrier D ⊆ F := by
  obtain ⟨hD,hab,hbc,hca,hwab,hwbc,hwca⟩ := of_decide_eq_true h
  have hD' : (0:ℝ) < rationalCross w.a w.b w.c := by exact_mod_cast hD
  rw [rationalCross_cast] at hD'
  intro p hp
  exact triangle_mem_convex F hF _ _ _ p ha hb hc hD'
    (w.ab.sound w.a w.b hab p (w.wab.sound D w.ab.plane hwab hp))
    (w.bc.sound w.b w.c hbc p (w.wbc.sound D w.bc.plane hwbc hp))
    (w.ca.sound w.c w.a hca p (w.wca.sound D w.ca.plane hwca hp))

theorem TriangleCertificate.hull_sound (w : TriangleCertificate) (D : List IntegerPlane)
    (h : w.check D = true) : IntegerCarrier D ⊆ rationalHull [w.a,w.b,w.c] := by
  apply w.sound D h _ (convex_convexHull ℝ _)
  · exact subset_convexHull ℝ _ ⟨w.a,by simp,rfl⟩
  · exact subset_convexHull ℝ _ ⟨w.b,by simp,rfl⟩
  · exact subset_convexHull ℝ _ ⟨w.c,by simp,rfl⟩

end
end ElevenSquare.Pending.T03
