import ElevenSquare.Pending.Types
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Closed polyhedral coverage using only integer arithmetic in finite checks.
Natural weights remove sign checks. Missing source indices denote the tautology
0 ≤ 0, so they cannot manufacture an implication. Target indices are checked.
Positive target multipliers clear denominators without division at cover leaves. -/
namespace ElevenSquare.Tasks.T02.IntegerCover
open ElevenSquare.Pending
noncomputable section

structure Plane where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

def Plane.contains (h : Plane) (p : Point) : Prop :=
  (h.a : ℝ) * p.1 + (h.b : ℝ) * p.2 ≤ h.c

abbrev Poly := List Plane
def Poly.carrier (hs : Poly) : Set Point := {p | ∀ h ∈ hs, h.contains p}
def zero : Plane := ⟨0, 0, 0⟩
def flip (h : Plane) : Plane := ⟨-h.a, -h.b, -h.c⟩
abbrev Combination := List (ℕ × ℕ)

def combinationSum (hs : Poly) : Combination → Plane
  | [] => zero
  | (i, w) :: ws =>
    let h := hs.getD i zero
    let s := combinationSum hs ws
    ⟨w * h.a + s.a, w * h.b + s.b, w * h.c + s.c⟩

theorem combination_sum_sound (hs : Poly) (ws : Combination)
    (p : Point) (hp : p ∈ hs.carrier) : (combinationSum hs ws).contains p := by
  induction ws with
  | nil => simp [combinationSum, zero, Plane.contains]
  | cons iw ws ih =>
    have hh : (hs.getD iw.1 zero).contains p := by
      by_cases hi : iw.1 < hs.length
      · apply hp
        rw [List.getD_eq_getElem hs zero hi]
        exact List.get_mem ..
      · rw [List.getD_eq_default hs zero (Nat.le_of_not_lt hi)]
        simp [zero, Plane.contains]
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg iw.2 : (0 : ℝ) ≤ iw.2)
    rcases iw with ⟨i, w⟩
    dsimp [combinationSum, Plane.contains] at hh' ih ⊢
    push_cast
    nlinarith

structure Implication where
  scale : ℕ
  weights : Combination

def Implication.Check (hs : Poly) (h : Plane) (w : Implication) : Prop :=
  0 < w.scale ∧
  (combinationSum hs w.weights).a = w.scale * h.a ∧
  (combinationSum hs w.weights).b = w.scale * h.b ∧
  (combinationSum hs w.weights).c ≤ w.scale * h.c

instance (hs : Poly) (h : Plane) (w : Implication) : Decidable (w.Check hs h) := by
  unfold Implication.Check
  infer_instance

theorem implication_sound (hs : Poly) (h : Plane) (w : Implication)
    (hc : w.Check hs h) (p : Point) (hp : p ∈ hs.carrier) : h.contains p := by
  have ha := combination_sum_sound hs w.weights p hp
  dsimp [Plane.contains] at ha ⊢
  rw [hc.2.1, hc.2.2.1] at ha
  have hb : ((combinationSum hs w.weights).c : ℝ) ≤ (w.scale : ℝ) * h.c := by
    exact_mod_cast hc.2.2.2
  have hspos : (0 : ℝ) < w.scale := by exact_mod_cast hc.1
  push_cast at ha
  nlinarith

def EmptyCheck (hs : Poly) (w : Combination) : Prop :=
  (combinationSum hs w).a = 0 ∧ (combinationSum hs w).b = 0 ∧
  (combinationSum hs w).c < 0

instance (hs : Poly) (w : Combination) : Decidable (EmptyCheck hs w) := by
  unfold EmptyCheck
  infer_instance

theorem empty_sound (hs : Poly) (w : Combination) (hc : EmptyCheck hs w)
    (p : Point) (hp : p ∈ hs.carrier) : False := by
  have ha := combination_sum_sound hs w p hp
  dsimp [Plane.contains] at ha
  rw [hc.1, hc.2.1] at ha
  norm_num at ha
  exact (not_lt_of_ge ha) hc.2.2

def PolygonCheck (source target : Poly) (ws : List Implication) : Prop :=
  target.length = ws.length ∧ ∀ hw ∈ target.zip ws, hw.2.Check source hw.1

instance (source target : Poly) (ws : List Implication) :
    Decidable (PolygonCheck source target ws) := by
  unfold PolygonCheck
  infer_instance

theorem polygon_sound (source target : Poly) (ws : List Implication)
    (hc : PolygonCheck source target ws) : source.carrier ⊆ target.carrier := by
  intro p hp
  induction target generalizing ws with
  | nil => intro h hh; simp at hh
  | cons h target ih =>
    cases ws with
    | nil => simp [PolygonCheck] at hc
    | cons w ws =>
      have hcheck : w.Check source h := hc.2 (h, w) (by simp)
      have htail : PolygonCheck source target ws := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro e he
        exact hc.2 e (by simp [he])
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact implication_sound source _ w hcheck p hp
      · exact ih ws htail g hg

inductive Certificate where
  | empty (w : Combination)
  | hit (index : ℕ) (w : List Implication)
  | split (h : Plane) (left right : Certificate)

def Certificate.Check (source : Poly) (targets : List Poly) : Certificate → Prop
  | .empty w => EmptyCheck source w
  | .hit i ws => i < targets.length ∧ PolygonCheck source (targets.getD i []) ws
  | .split h l r => l.Check (h :: source) targets ∧ r.Check (flip h :: source) targets

instance (source : Poly) (targets : List Poly) (c : Certificate) :
    Decidable (c.Check source targets) := by
  induction c generalizing source with
  | empty w => exact inferInstanceAs (Decidable (EmptyCheck _ _))
  | hit i w => exact inferInstanceAs (Decidable (_ ∧ PolygonCheck _ _ _))
  | split h l r il ir =>
    letI := il (h :: source)
    letI := ir (flip h :: source)
    exact inferInstanceAs (Decidable (_ ∧ _))

theorem certificate_sound (source : Poly) (targets : List Poly) (c : Certificate)
    (hc : c.Check source targets) (p : Point) (hp : p ∈ source.carrier) :
    ∃ t ∈ targets, p ∈ t.carrier := by
  induction c generalizing source with
  | empty w => exact (empty_sound source w hc p hp).elim
  | hit i ws =>
    refine ⟨targets.getD i [], ?_, polygon_sound _ _ ws hc.2 hp⟩
    rw [List.getD_eq_getElem targets [] hc.1]
    exact List.get_mem ..
  | split h l r il ir =>
    by_cases hin : h.contains p
    · apply il (h :: source) hc.1
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hin
      · exact hp g hg
    · apply ir (flip h :: source) hc.2
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · dsimp [flip, Plane.contains] at hin ⊢
        push_cast
        linarith
      · exact hp g hg

end
end ElevenSquare.Tasks.T02.IntegerCover
