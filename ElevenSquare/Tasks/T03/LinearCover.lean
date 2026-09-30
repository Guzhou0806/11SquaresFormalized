import ElevenSquare.Tasks.T03.LinearCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def IntegerPlane.flip (l : IntegerPlane) : IntegerPlane := ⟨-l.a,-l.b,-l.c⟩

theorem IntegerPlane.flip_of_not_holds (l : IntegerPlane) (p : Point)
    (h : ¬ l.holds p) : l.flip.holds p := by
  dsimp [IntegerPlane.holds, IntegerPlane.flip] at *
  push_cast
  linarith

theorem integerCarrier_cons (l : IntegerPlane) (ls : List IntegerPlane) (p : Point) :
    p ∈ IntegerCarrier (l::ls) ↔ l.holds p ∧ p ∈ IntegerCarrier ls := by
  simp [IntegerCarrier]

/-- A closed binary split retains the cutting line on both sides. -/
theorem linear_cover_split (D : List IntegerPlane) (l : IntegerPlane) (F : Set Point)
    (left : IntegerCarrier (l::D) ⊆ F) (right : IntegerCarrier (l.flip::D) ⊆ F) :
    IntegerCarrier D ⊆ F := by
  intro p hp
  by_cases h : l.holds p
  · exact left ((integerCarrier_cons l D p).mpr ⟨h,hp⟩)
  · exact right ((integerCarrier_cons l.flip D p).mpr ⟨l.flip_of_not_holds p h,hp⟩)

theorem linear_cover_empty (D : List IntegerPlane) (F : Set Point)
    (w : LinearCertificate) (h : w.check D ⟨0,0,-1⟩ = true) : IntegerCarrier D ⊆ F := by
  rw [w.empty D h]
  exact Set.empty_subset F

theorem integerCarrier_implies_constraints (D R : List IntegerPlane)
    (h : ∀ l ∈ R, ∃ w : LinearCertificate, w.check D l = true) :
    IntegerCarrier D ⊆ IntegerCarrier R := by
  intro p hp l hl
  obtain ⟨w,hw⟩ := h l hl
  exact w.sound D l hw hp

theorem linear_cover_region (D R : List IntegerPlane) (F : Set Point)
    (h : ∀ l ∈ R, ∃ w : LinearCertificate, w.check D l = true)
    (hR : IntegerCarrier R ⊆ F) : IntegerCarrier D ⊆ F :=
  (integerCarrier_implies_constraints D R h).trans hR

end
end ElevenSquare.Pending.T03
