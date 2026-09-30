import ElevenSquare.BasicGeometry
import ElevenSquare.Orientation
import ElevenSquare.CoverData
import ElevenSquare.EndpointBounds
import Mathlib.Tactic.FieldSimp

/-! Rigid transport between container frames. Only the certificate coordinates
are divided by `fieldScale`; an actual physical unit square is never scaled. -/
namespace ElevenSquare.Tasks.T07
noncomputable section

/-- A centered subcontainer of side `S` in a coordinate frame of side `U`. -/
def InCenteredContainer (U S : ℝ) (p : Point) : Prop :=
  |p.1-U/2| ≤ S/2 ∧ |p.2-U/2| ≤ S/2

/-- Whole-square containment, not just a condition on square centers. -/
def CenteredPacking {n : ℕ} {U : ℝ} (P : Packing n U) (S : ℝ) : Prop :=
  ∀ i p, ClosedSquare (P.squares i) p → InCenteredContainer U S p

theorem centeredContainer_mono {U S V : ℝ} {p : Point}
    (hSV : S ≤ V) (h : InCenteredContainer U S p) :
    InCenteredContainer U V p := by
  exact ⟨h.1.trans (by linarith), h.2.trans (by linarith)⟩

theorem centeredContainer_self_iff (U : ℝ) (p : Point) :
    InCenteredContainer U U p ↔ InContainer U p := by
  simp only [InCenteredContainer, abs_le, InContainer]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem enlargeCentered_preserves_side {n : ℕ} {S U : ℝ}
    (P : Packing n S) (hSU : S ≤ U) :
    CenteredPacking (P.enlargeCentered hSU) S := by
  intro i p hp
  have h := P.contained i (p-((U-S)/2,(U-S)/2))
    ((closed_translated _ _ _).mp hp)
  rcases h with ⟨hx0, hx1, hy0, hy1⟩
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at hx0 hx1 hy0 hy1
  apply And.intro <;> apply abs_le.mpr
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/-- Clockwise quarter-turn about the old center, then translation to the new
container center. This is a rigid map for every `U` and `V`. -/
def quarterTo (U V : ℝ) (p : Point) : Point :=
  (p.2+(V-U)/2, (U+V)/2-p.1)

def quarterFrom (U V : ℝ) (p : Point) : Point :=
  ((U+V)/2-p.2, p.1+(U-V)/2)

@[simp] theorem quarterFrom_quarterTo (U V : ℝ) (p : Point) :
    quarterFrom U V (quarterTo U V p) = p := by
  apply Prod.ext <;> dsimp [quarterFrom, quarterTo] <;> ring

@[simp] theorem quarterTo_quarterFrom (U V : ℝ) (p : Point) :
    quarterTo U V (quarterFrom U V p) = p := by
  apply Prod.ext <;> dsimp [quarterFrom, quarterTo] <;> ring

theorem quarterTo_injective (U V : ℝ) : Function.Injective (quarterTo U V) := by
  intro p q h
  have h' := congrArg (quarterFrom U V) h
  simpa only [quarterFrom_quarterTo] using h'

theorem quarterTo_surjective (U V : ℝ) : Function.Surjective (quarterTo U V) := by
  intro p
  exact ⟨quarterFrom U V p, quarterTo_quarterFrom U V p⟩

theorem quarterTo_centered (U V S : ℝ) (p : Point) :
    InCenteredContainer V S (quarterTo U V p) ↔ InCenteredContainer U S p := by
  have hx : (quarterTo U V p).1-V/2 = p.2-U/2 := by dsimp [quarterTo]; ring
  have hy : (quarterTo U V p).2-V/2 = -(p.1-U/2) := by dsimp [quarterTo]; ring
  simp only [InCenteredContainer, hx, hy, abs_neg]
  exact and_comm

def quarterSquare (U V : ℝ) (q : UnitSquare) : UnitSquare where
  center := quarterTo U V q.center
  axis := (q.axis.2, -q.axis.1)
  axis_unit := by
    have h := q.axis_unit
    dsimp [normSq, dot] at h ⊢
    nlinarith

theorem quarterSquare_localX (U V : ℝ) (q : UnitSquare) (p : Point) :
    localX (quarterSquare U V q) (quarterTo U V p) = localX q p := by
  dsimp [quarterSquare, quarterTo, localX, dot]
  ring

theorem quarterSquare_localY (U V : ℝ) (q : UnitSquare) (p : Point) :
    localY (quarterSquare U V q) (quarterTo U V p) = localY q p := by
  dsimp [quarterSquare, quarterTo, localY, dot, perp]
  ring

theorem quarterSquare_closed (U V : ℝ) (q : UnitSquare) (p : Point) :
    ClosedSquare (quarterSquare U V q) (quarterTo U V p) ↔ ClosedSquare q p := by
  simp only [ClosedSquare, quarterSquare_localX, quarterSquare_localY]

theorem quarterSquare_open (U V : ℝ) (q : UnitSquare) (p : Point) :
    OpenSquare (quarterSquare U V q) (quarterTo U V p) ↔ OpenSquare q p := by
  simp only [OpenSquare, quarterSquare_localX, quarterSquare_localY]

/-- A physically smaller centered packing can be transported into the exact
local frame without dilating any of its squares. -/
def quarterPacking {n : ℕ} {U V S : ℝ} (P : Packing n U)
    (hV : 0 ≤ V) (hsmall : CenteredPacking P S) (hSV : S ≤ V) : Packing n V where
  squares i := quarterSquare U V (P.squares i)
  side_nonneg := hV
  contained := by
    intro i p hp
    obtain ⟨q, rfl⟩ := quarterTo_surjective U V p
    apply (centeredContainer_self_iff V _).mp
    apply centeredContainer_mono hSV
    exact (quarterTo_centered U V S q).mpr
      (hsmall i q ((quarterSquare_closed U V _ q).mp hp))
  interior_disjoint := by
    intro i j hij p hp
    obtain ⟨q, rfl⟩ := quarterTo_surjective U V p
    exact P.interior_disjoint i j hij q
      ⟨(quarterSquare_open U V _ q).mp hp.1,
       (quarterSquare_open U V _ q).mp hp.2⟩


theorem quarterPacking_centered {n : ℕ} {U V S : ℝ} (P : Packing n U)
    (hV : 0 ≤ V) (hsmall : CenteredPacking P S) (hSV : S ≤ V) :
    CenteredPacking (quarterPacking P hV hsmall hSV) S := by
  intro i p hp
  obtain ⟨q, rfl⟩ := quarterTo_surjective U V p
  exact (quarterTo_centered U V S q).mpr
    (hsmall i q ((quarterSquare_closed U V _ q).mp hp))

/-- Square equality does not require identifying the proof field `axis_unit`. -/
theorem unitSquare_ext {q r : UnitSquare}
    (hc : q.center = r.center) (ha : q.axis = r.axis) : q = r := by
  cases q with
  | mk qc qa hq =>
    cases r with
    | mk rc ra hr =>
      dsimp at hc ha
      subst rc
      subst ra
      rfl

/-- Replace representatives of the same actual squares. -/
def replaceSquares {n : ℕ} {U : ℝ} (P : Packing n U)
    (r : Fin n → UnitSquare) (hsame : ∀ i, SameSquare (P.squares i) (r i)) :
    Packing n U where
  squares := r
  side_nonneg := P.side_nonneg
  contained i p hp := P.contained i p ((hsame i).closed_iff p |>.mpr hp)
  interior_disjoint := by
    intro i j hij p hp
    exact P.interior_disjoint i j hij p
      ⟨((hsame i).open_iff p).mpr hp.1, ((hsame j).open_iff p).mpr hp.2⟩

theorem replaceSquares_centered {n : ℕ} {U S : ℝ} (P : Packing n U)
    (r : Fin n → UnitSquare) (hsame : ∀ i, SameSquare (P.squares i) (r i))
    (hsmall : CenteredPacking P S) : CenteredPacking (replaceSquares P r hsame) S := by
  intro i p hp
  exact hsmall i p (((hsame i).closed_iff p).mpr hp)

/-- This scale belongs to the rational certificate field, not the physical
unit-square geometry. -/
def fieldScale : ℝ := (191/50)/coverCap

theorem coverCap_pos : 0 < coverCap := by norm_num [coverCap]

theorem fieldScale_pos : 0 < fieldScale := by
  exact div_pos (by norm_num) coverCap_pos

theorem fieldScale_ne_zero : fieldScale ≠ 0 := ne_of_gt fieldScale_pos

/-- Exact formula used by the case-438 capture data. -/
def fieldToLocal (p : Point) : Point :=
  (p.2/fieldScale-coverCap/2+T/2, coverCap/2-p.1/fieldScale+T/2)

def toField (p : Point) : Point := (fieldScale*p.1, fieldScale*p.2)

theorem fieldToLocal_toField (p : Point) :
    fieldToLocal (toField p) = quarterTo coverCap T p := by
  apply Prod.ext <;> dsimp [fieldToLocal, toField, quarterTo] <;>
    field_simp [fieldScale_ne_zero] <;> ring

theorem fieldToLocal_exact (p : Point) :
    fieldToLocal p = quarterTo coverCap T (p.1/fieldScale,p.2/fieldScale) := by
  apply Prod.ext <;> dsimp [fieldToLocal, quarterTo] <;> ring

end
end ElevenSquare.Tasks.T07
