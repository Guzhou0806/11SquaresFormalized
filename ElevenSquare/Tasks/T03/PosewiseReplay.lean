import ElevenSquare.Tasks.T03.TraceAssembly
import ElevenSquare.Tasks.T03.Certificate

namespace ElevenSquare.Pending.T03
noncomputable section

/-- The partner is fixed for the discarded pose, and every admissible partner
pose is quantified. Ownership premises retain their actual state context. -/
def CollisionPose (prior : Owner → List QPoint) (rows : Owner → List PoseRow)
    (i : Owner) (q : UnitSquare) : Prop :=
  ∃ j : Owner, i ≠ j ∧ ∀ r : UnitSquare, RowsContain (rows j) r →
    (rationalHull (prior j) ⊆ {p | OpenSquare r p}) →
    ∃ p, OpenSquare q p ∧ OpenSquare r p

/-- A semantic row replay stores both the old hull and partner row contexts.
It permits a different universally colliding region for each source pose. -/
structure ReplayRows (prior : Owner → List QPoint) (rows : Owner → List PoseRow)
    (i : Owner) (chosen : List QPoint) where
  before : List PoseRow
  after : List PoseRow
  back : ∀ q, RowsContain after q → RowsContain before q
  cover : ∀ q, RowsContain before q →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
    RowsContain after q ∨ ForbiddenPose prior i q ∨ CollisionPose prior rows i q
  owned : ∀ q, RowsContain after q →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
    ∀ p ∈ chosen, OpenSquare q (realPoint p)

def ReplayRows.ofRowsCertificate {prior : Owner → List QPoint} {i : Owner}
    {chosen : List QPoint} (w : RowsCertificate prior i chosen)
    (rows : Owner → List PoseRow) : ReplayRows prior rows i chosen where
  before := w.before
  after := w.after
  back := w.back
  cover := by
    intro q hq hold
    exact (w.cover q hq hold).imp id Or.inl
  owned := w.owned

def ReplayRows.append {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
    {i : Owner} {chosen : List QPoint}
    (a b : ReplayRows prior rows i chosen) : ReplayRows prior rows i chosen where
  before := a.before++b.before
  after := a.after++b.after
  back := by
    intro q hq
    rw [rowsContain_append] at hq ⊢
    exact hq.elim (fun h => Or.inl (a.back q h)) (fun h => Or.inr (b.back q h))
  cover := by
    intro q hq hold
    rw [rowsContain_append] at hq
    rcases hq with ha | hb
    · exact (a.cover q ha hold).imp
        (fun h => (rowsContain_append _ _ q).mpr (Or.inl h)) id
    · exact (b.cover q hb hold).imp
        (fun h => (rowsContain_append _ _ q).mpr (Or.inr h)) id
  owned := by
    intro q hq hold
    rw [rowsContain_append] at hq
    exact hq.elim (fun h => a.owned q h hold) (fun h => b.owned q h hold)

/-- Check the complete transition for an arbitrary packing, using frozen
promotion soundness and the packing's interior-disjointness invariant. -/
theorem ReplayRows.sound {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
    {i : Owner} {chosen : List QPoint} (w : ReplayRows prior rows i chosen)
    (s : PoseState) (hprior : s.owned=prior) (hpartners : s.rows=rows)
    (hbefore : s.rows i=w.before) {S : ℝ} (P : Packing 11 S) (hs : StateHolds P s) :
    StateHolds P (replaceHull (replaceRows s i w.after) i chosen) := by
  have hq : RowsContain w.before (P.squares i) := by rw [← hbefore]; exact hs.1 i
  have hold : rationalHull (prior i) ⊆ {p | OpenSquare (P.squares i) p} := by
    rw [← hprior]; exact hs.2 i
  have hkeep : RowsContain w.after (P.squares i) := by
    rcases w.cover (P.squares i) hq hold with hk | hf | hj
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
      obtain ⟨p,hp⟩ := hall (P.squares j) hjrow hjold
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

end
end ElevenSquare.Pending.T03
