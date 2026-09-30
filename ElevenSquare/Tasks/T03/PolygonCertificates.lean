import ElevenSquare.Tasks.T03.TriangleCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def triangleVerticesCheck (w : TriangleCertificate) (vs : List QPoint) : Bool :=
  decide (w.a ∈ vs ∧ w.b ∈ vs ∧ w.c ∈ vs)

inductive TriangleCoverTree where
  | triangle (certificate : TriangleCertificate)
  | empty (certificate : LinearCertificate)
  | split (plane : IntegerPlane) (left right : TriangleCoverTree)

def TriangleCoverTree.check : TriangleCoverTree → List IntegerPlane → List QPoint → Bool
  | .triangle w, D, vs => w.check D && triangleVerticesCheck w vs
  | .empty w, D, _ => w.check D ⟨0,0,-1⟩
  | .split l left right, D, vs => left.check (l::D) vs && right.check (l.flip::D) vs

theorem TriangleCoverTree.sound (w : TriangleCoverTree) (D : List IntegerPlane)
    (vs : List QPoint) (h : w.check D vs = true) : IntegerCarrier D ⊆ rationalHull vs := by
  induction w generalizing D with
  | triangle w =>
    simp only [TriangleCoverTree.check,Bool.and_eq_true] at h
    obtain ⟨ha,hb,hc⟩ := of_decide_eq_true h.2
    exact w.sound D h.1 _ (convex_convexHull ℝ _)
      (subset_convexHull ℝ _ ⟨w.a,ha,rfl⟩)
      (subset_convexHull ℝ _ ⟨w.b,hb,rfl⟩)
      (subset_convexHull ℝ _ ⟨w.c,hc,rfl⟩)
  | empty w => exact linear_cover_empty D _ w h
  | split l left right ihl ihr =>
    simp only [TriangleCoverTree.check,Bool.and_eq_true] at h
    exact linear_cover_split D l _ (ihl (l::D) h.1) (ihr (l.flip::D) h.2)

theorem TriangleCoverTree.triangle_checked (w : TriangleCertificate) (D : List IntegerPlane)
    (vs : List QPoint) (hc : w.check D = true) (hv : triangleVerticesCheck w vs = true) :
    (TriangleCoverTree.triangle w).check D vs = true := by
  simp only [TriangleCoverTree.check,hc,hv,Bool.and_self]

theorem TriangleCoverTree.split_checked (l : IntegerPlane) (left right : TriangleCoverTree)
    (D : List IntegerPlane) (vs : List QPoint)
    (hl : left.check (l::D) vs = true) (hr : right.check (l.flip::D) vs = true) :
    (TriangleCoverTree.split l left right).check D vs = true := by
  simp only [TriangleCoverTree.check,hl,hr,Bool.and_self]

def planeImplicationsCheck (D : List IntegerPlane) :
    List IntegerPlane → List LinearCertificate → Bool
  | [], [] => true
  | l::ls, w::ws => w.check D l && planeImplicationsCheck D ls ws
  | _, _ => false

theorem planeImplicationsCheck_sound (D R : List IntegerPlane) (ws : List LinearCertificate)
    (h : planeImplicationsCheck D R ws = true) : IntegerCarrier D ⊆ IntegerCarrier R := by
  induction R generalizing ws with
  | nil => intro p hp l hl; cases hl
  | cons l ls ih =>
    cases ws with
    | nil => simp [planeImplicationsCheck] at h
    | cons w ws =>
      simp only [planeImplicationsCheck,Bool.and_eq_true] at h
      intro p hp k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact w.sound D k h.1 hp
      · exact ih ws h.2 hp k hk

inductive RegionCoverTree where
  | region (planes : List IntegerPlane) (certificates : List LinearCertificate)
  | empty (certificate : LinearCertificate)
  | split (plane : IntegerPlane) (left right : RegionCoverTree)

def regionMemberCheck (R : List IntegerPlane) (regions : List (List IntegerPlane)) : Bool :=
  decide (R ∈ regions)

def RegionCoverTree.check : RegionCoverTree → List IntegerPlane → List (List IntegerPlane) → Bool
  | .region R ws, D, regions => planeImplicationsCheck D R ws && regionMemberCheck R regions
  | .empty w, D, _ => w.check D ⟨0,0,-1⟩
  | .split l left right, D, regions => left.check (l::D) regions && right.check (l.flip::D) regions

theorem RegionCoverTree.sound (w : RegionCoverTree) (D : List IntegerPlane)
    (regions : List (List IntegerPlane)) (F : Set Point) (h : w.check D regions = true)
    (hregions : ∀ R ∈ regions, IntegerCarrier R ⊆ F) : IntegerCarrier D ⊆ F := by
  induction w generalizing D with
  | region R ws =>
    simp only [RegionCoverTree.check,Bool.and_eq_true] at h
    exact (planeImplicationsCheck_sound D R ws h.1).trans (hregions R (of_decide_eq_true h.2))
  | empty w => exact linear_cover_empty D F w h
  | split l left right ihl ihr =>
    simp only [RegionCoverTree.check,Bool.and_eq_true] at h
    exact linear_cover_split D l F (ihl (l::D) h.1) (ihr (l.flip::D) h.2)

theorem RegionCoverTree.region_checked (R D : List IntegerPlane) (ws : List LinearCertificate)
    (regions : List (List IntegerPlane)) (hw : planeImplicationsCheck D R ws = true)
    (hm : regionMemberCheck R regions = true) :
    (RegionCoverTree.region R ws).check D regions = true := by
  simp only [RegionCoverTree.check,hw,hm,Bool.and_self]

theorem RegionCoverTree.split_checked (l : IntegerPlane) (left right : RegionCoverTree)
    (D : List IntegerPlane) (regions : List (List IntegerPlane))
    (hl : left.check (l::D) regions = true) (hr : right.check (l.flip::D) regions = true) :
    (RegionCoverTree.split l left right).check D regions = true := by
  simp only [RegionCoverTree.check,hl,hr,Bool.and_self]

end
end ElevenSquare.Pending.T03
