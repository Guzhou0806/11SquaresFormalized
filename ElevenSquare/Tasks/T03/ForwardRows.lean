import ElevenSquare.Tasks.T03.PosewiseReplay
import ElevenSquare.Tasks.T03.IntegerRowTrace

namespace ElevenSquare.Pending.T03
noncomputable section

def ContainedAtCap (q : UnitSquare) : Prop :=
  ∀ p, ClosedSquare q p → InContainer coverCap p

def PhysicalCollisionPose (prior : Owner → List QPoint) (rows : Owner → List PoseRow)
    (i : Owner) (q : UnitSquare) : Prop :=
  ∃ j : Owner, i ≠ j ∧ ∀ r : UnitSquare, RowsContain (rows j) r → ContainedAtCap r →
    (rationalHull (prior j) ⊆ {p | OpenSquare r p}) →
    ∃ p, OpenSquare q p ∧ OpenSquare r p

/-- A forward update retains the exact owned-hull and partner-row contexts.
It may replace a row by a larger convex enclosure, so no backward inclusion
is required. All pruning and promotion obligations remain explicit. -/
structure ForwardRows (prior : Owner → List QPoint) (rows : Owner → List PoseRow)
    (i : Owner) (chosen : List QPoint) where
  before : List PoseRow
  after : List PoseRow
  cover : ∀ q, RowsContain before q → ContainedAtCap q →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
    RowsContain after q ∨ ForbiddenPose prior i q ∨ PhysicalCollisionPose prior rows i q
  owned : ∀ q, RowsContain after q →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
    ∀ p ∈ chosen, OpenSquare q (realPoint p)

def ForwardRows.append {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
    {i : Owner} {chosen : List QPoint}
    (a b : ForwardRows prior rows i chosen) : ForwardRows prior rows i chosen where
  before := a.before++b.before
  after := a.after++b.after
  cover := by
    intro q hq hcap hold
    rw [rowsContain_append] at hq
    rcases hq with ha | hb
    · exact (a.cover q ha hcap hold).imp
        (fun h => (rowsContain_append _ _ q).mpr (Or.inl h)) id
    · exact (b.cover q hb hcap hold).imp
        (fun h => (rowsContain_append _ _ q).mpr (Or.inr h)) id
  owned := by
    intro q hq hold
    rw [rowsContain_append] at hq
    exact hq.elim (fun h => a.owned q h hold) (fun h => b.owned q h hold)

theorem ForwardRows.sound {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
    {i : Owner} {chosen : List QPoint} (w : ForwardRows prior rows i chosen)
    (s : PoseState) (hprior : s.owned=prior) (hpartners : s.rows=rows)
    (hbefore : s.rows i=w.before) (P : Packing 11 coverCap) (hs : StateHolds P s) :
    StateHolds P (replaceHull (replaceRows s i w.after) i chosen) := by
  have hq : RowsContain w.before (P.squares i) := by rw [← hbefore]; exact hs.1 i
  have hold : rationalHull (prior i) ⊆ {p | OpenSquare (P.squares i) p} := by
    rw [← hprior]; exact hs.2 i
  have hkeep : RowsContain w.after (P.squares i) := by
    rcases w.cover (P.squares i) hq (P.contained i) hold with hk | hf | hj
    · exact hk
    · rcases hf with ⟨j,hij,Q,hQ,hf⟩
      have hjold : rationalHull (prior j) ⊆ {p | OpenSquare (P.squares j) p} := by
        rw [← hprior]; exact hs.2 j
      obtain ⟨p,hp⟩ := forbidden_center_implies_overlap
        (P.squares i) (P.squares j) (rationalHull (prior j)) Q hjold hQ hf
      exact False.elim (P.interior_disjoint i j hij p hp)
    · rcases hj with ⟨j,hij,hall⟩
      have hjrow : RowsContain (rows j) (P.squares j) := by rw [← hpartners]; exact hs.1 j
      have hjold : rationalHull (prior j) ⊆ {p | OpenSquare (P.squares j) p} := by
        rw [← hprior]; exact hs.2 j
      obtain ⟨p,hp⟩ := hall (P.squares j) hjrow (P.contained j) hjold
      exact False.elim (P.interior_disjoint i j hij p hp)
  have hpruned : StateHolds P (replaceRows s i w.after) := by
    refine ⟨?_,hs.2⟩
    intro j
    by_cases hji : j=i
    · subst j; simpa only [replaceRows,Function.update_same] using hkeep
    · simpa only [replaceRows,Function.update_noteq hji] using hs.1 j
  apply verified_step_sound P hpruned
  apply VerifiedStep.promoteOwned
  intro q hrow hown
  have hrow' : RowsContain w.after q := by
    simpa only [replaceRows,Function.update_same] using hrow
  have hown' : rationalHull (prior i) ⊆ {p | OpenSquare q p} := by
    simpa only [replaceRows,hprior] using hown
  exact w.owned q hrow' hown'

structure ForwardRowGeometry (prior : Owner → List QPoint) (rows : Owner → List PoseRow)
    (i : Owner) (chosen : List QPoint) where
  lo : ℚ
  hi : ℚ
  global_bounds : 0 ≤ lo ∧ hi ≤ 1
  domain : List IntegerPlane
  kept : Option (List IntegerPlane)
  cover : ∀ q t, (lo:ℝ) ≤ t → t ≤ (hi:ℝ) → q.axis=chartAxis t →
    q.center ∈ IntegerCarrier domain →
    keptCenter kept q.center ∨ ForbiddenPose prior i q ∨ PhysicalCollisionPose prior rows i q
  owned : ∀ q t, (lo:ℝ) ≤ t → t ≤ (hi:ℝ) → q.axis=chartAxis t →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) → keptCenter kept q.center →
    ∀ p ∈ chosen, OpenSquare q (realPoint p)

def ForwardRowGeometry.ofRowGeometry {prior : Owner → List QPoint} {i : Owner}
    {chosen : List QPoint} (g : RowGeometry prior i chosen)
    (rows : Owner → List PoseRow) (hb : 0 ≤ g.lo ∧ g.hi ≤ 1) :
    ForwardRowGeometry prior rows i chosen where
  lo := g.lo
  hi := g.hi
  global_bounds := hb
  domain := g.domain
  kept := g.kept
  cover := fun q t ha hb hq hc => (g.cover q t ha hb hq hc).imp id Or.inl
  owned := g.owned

def ForwardRowGeometry.resultRows {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
    {i : Owner} {chosen : List QPoint} (g : ForwardRowGeometry prior rows i chosen) : List PoseRow :=
  match g.kept with
  | none => []
  | some ls => [⟨g.lo,g.hi,ls.map IntegerPlane.rational⟩]

theorem ForwardRowGeometry.result_contains {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
    {i : Owner} {chosen : List QPoint} (g : ForwardRowGeometry prior rows i chosen) (q : UnitSquare) :
    RowsContain g.resultRows q ↔ keptCenter g.kept q.center ∧
      ∃ t : ℝ, (g.lo:ℝ) ≤ t ∧ t ≤ (g.hi:ℝ) ∧ q.axis=chartAxis t := by
  cases h : g.kept with
  | none => simp [resultRows,h,RowsContain,keptCenter]
  | some ls =>
    simp only [resultRows,h,rowsContain_singleton,keptCenter]
    constructor
    · rintro ⟨hc,t,_,_,ha,hb,hq⟩
      refine ⟨?_,t,ha,hb,hq⟩
      rwa [integerCarrier_as_polygon]
    · rintro ⟨hc,t,ha,hb,hq⟩
      have h0 : (0:ℝ) ≤ g.lo := by exact_mod_cast g.global_bounds.1
      have h1 : (g.hi:ℝ) ≤ 1 := by exact_mod_cast g.global_bounds.2
      refine ⟨?_,t,le_trans h0 ha,le_trans hb h1,ha,hb,hq⟩
      rwa [← integerCarrier_as_polygon]

def ForwardRowGeometry.certificate {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
    {i : Owner} {chosen : List QPoint} (g : ForwardRowGeometry prior rows i chosen) (r : IntegerRow)
    (input : ∀ q, r.row.contains q → ContainedAtCap q →
      (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
      q.center ∈ IntegerCarrier g.domain ∧
        ∃ t : ℝ, (g.lo:ℝ) ≤ t ∧ t ≤ (g.hi:ℝ) ∧ q.axis=chartAxis t) :
    ForwardRows prior rows i chosen where
  before := [r.row]
  after := g.resultRows
  cover := by
    intro q hq hcap hold
    obtain ⟨hc,t,ha,hb,haxis⟩ := input q ((rowsContain_singleton _ q).mp hq) hcap hold
    rcases g.cover q t ha hb haxis hc with hk | hf
    · exact Or.inl ((g.result_contains q).mpr ⟨hk,t,ha,hb,haxis⟩)
    · exact Or.inr hf
  owned := by
    intro q hq hold
    obtain ⟨hc,t,ha,hb,haxis⟩ := (g.result_contains q).mp hq
    exact g.owned q t ha hb haxis hold hc

end
end ElevenSquare.Pending.T03
