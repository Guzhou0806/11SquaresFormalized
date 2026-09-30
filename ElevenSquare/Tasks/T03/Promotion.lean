import ElevenSquare.Pending.S05_Trace
import ElevenSquare.Tasks.T03.Convexification

namespace ElevenSquare.Pending.T03
noncomputable section

/-- A certificate for one retained point. The core endpoint is certified against
all rows using the old ownership context, including any necessary self-hull cuts. -/
inductive ChosenPoint (old : List QPoint) (common : Set Point) (p : Point) : Prop
  | core (h : p ∈ common)
  | old (h : p ∈ rationalHull old)
  | mix (a b : Point) (weight : ℝ)
      (ha : a ∈ rationalHull old) (hb : b ∈ common)
      (h0 : 0 ≤ weight) (h1 : weight ≤ 1)
      (heq : p = (1-weight) • a + weight • b)

theorem chosenPoint_owned (q : UnitSquare) (old : List QPoint)
    (common : Set Point) (p : Point)
    (hold : rationalHull old ⊆ {p | OpenSquare q p})
    (hcommon : common ⊆ {p | OpenSquare q p})
    (h : ChosenPoint old common p) : OpenSquare q p := by
  cases h with
  | core hp => exact hcommon hp
  | old hp => exact hold hp
  | mix a b weight ha hb h0 h1 heq =>
    rw [heq]
    exact openSquare_convex q (hold ha) (hcommon hb)
      (sub_nonneg.mpr h1) h0 (sub_add_cancel 1 weight)

/-- Keep exactly the recorded downstream list. Old points can be retained by
using the `old` tag; no equality with a computed kernel polygon is assumed. -/
theorem promote_chosen (s : PoseState) (i : Owner)
    (common : Set Point) (vs : List QPoint)
    (hcommon : ∀ q, RowsContain (s.rows i) q →
      rationalHull (s.owned i) ⊆ {p | OpenSquare q p} →
      common ⊆ {p | OpenSquare q p})
    (hvs : ∀ v ∈ vs, ChosenPoint (s.owned i) common (realPoint v)) :
    VerifiedStep s (replaceHull s i vs) := by
  apply VerifiedStep.promoteOwned
  intro q hq hold v hv
  exact chosenPoint_owned q (s.owned i) common (realPoint v)
    hold (hcommon q hq hold) (hvs v hv)

/-- The old hull implies a necessary center cut for every square that owns it.
The ownership premise is explicit, and cannot be discarded during row pruning. -/
theorem selfHull_center_upper (q : UnitSquare) (vs : List QPoint)
    (hold : rationalHull vs ⊆ {p | OpenSquare q p})
    (v : QPoint) (hv : v ∈ vs) (n : Point) (E : ℝ)
    (hE : projectionRadius q n ≤ E) :
    dot q.center n ≤ dot (realPoint v) n + E := by
  have hvh : realPoint v ∈ rationalHull vs :=
    subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  have hop := hold hvh
  have hcl : ClosedSquare q (realPoint v) := ⟨hop.1.le, hop.2.le⟩
  have hb := closed_projection_bound hcl n
  have he : dot (realPoint v - q.center) n =
      dot (realPoint v) n - dot q.center n := by
    dsimp [dot]
    ring
  rw [he] at hb
  have hl := (abs_le.mp (hb.trans hE)).1
  linarith

end
end ElevenSquare.Pending.T03
