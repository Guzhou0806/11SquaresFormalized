import ElevenSquare.Tasks.T03.RowTrace
import ElevenSquare.Tasks.T03.IntegerRows

namespace ElevenSquare.Pending.T03
noncomputable section

def ForbiddenPose (prior : Owner → List QPoint) (i : Owner) (q : UnitSquare) : Prop :=
  ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
    CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (prior j)) Q

/-- A reusable row block retains the exact ownership context in its type. -/
structure RowsCertificate (prior : Owner → List QPoint) (i : Owner) (chosen : List QPoint) where
  before : List PoseRow
  after : List PoseRow
  back : ∀ q, RowsContain after q → RowsContain before q
  cover : ∀ q, RowsContain before q →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
    RowsContain after q ∨ ForbiddenPose prior i q
  owned : ∀ q, RowsContain after q →
    (rationalHull (prior i) ⊆ {p | OpenSquare q p}) →
    ∀ p ∈ chosen, OpenSquare q (realPoint p)

def RowsCertificate.append {prior : Owner → List QPoint} {i : Owner} {chosen : List QPoint}
    (a b : RowsCertificate prior i chosen) : RowsCertificate prior i chosen where
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
    · rcases a.cover q ha hold with hn | hf
      · exact Or.inl ((rowsContain_append _ _ q).mpr (Or.inl hn))
      · exact Or.inr hf
    · rcases b.cover q hb hold with hn | hf
      · exact Or.inl ((rowsContain_append _ _ q).mpr (Or.inr hn))
      · exact Or.inr hf
  owned := by
    intro q hq hold
    rw [rowsContain_append] at hq
    exact hq.elim (fun h => a.owned q h hold) (fun h => b.owned q h hold)

def RowsCertificate.empty (prior : Owner → List QPoint) (i : Owner) (chosen : List QPoint) :
    RowsCertificate prior i chosen where
  before := []
  after := []
  back := by intro q h; exact h
  cover := by intro q h; rcases h with ⟨r,hr,_⟩; cases hr
  owned := by intro q h; rcases h with ⟨r,hr,_⟩; cases hr

theorem RowsCertificate.trace {prior : Owner → List QPoint} {i : Owner} {chosen : List QPoint}
    (w : RowsCertificate prior i chosen) (s : PoseState) (hs : RowsOwn s)
    (hprior : s.owned = prior) (hrows : s.rows i = w.before) :
    VerifiedTrace s (replaceHull (replaceRows s i w.after) i chosen) ∧
    RowsOwn (replaceHull (replaceRows s i w.after) i chosen) := by
  have hback (q : UnitSquare) (hq : RowsContain w.after q) : RowsContain (s.rows i) q := by
    rw [hrows]; exact w.back q hq
  have hp : VerifiedStep s (replaceRows s i w.after) := by
    apply VerifiedStep.prunePosewise
    intro q hq
    have hold := hs i q hq
    rw [hprior] at hold
    rw [hrows] at hq
    simpa only [ForbiddenPose,hprior] using w.cover q hq hold
  have ho : RowsOwn (replaceRows s i w.after) := rowsOwn_replaceRows s i w.after hs hback
  have hv : ∀ q, RowsContain ((replaceRows s i w.after).rows i) q →
      rationalHull ((replaceRows s i w.after).owned i) ⊆ {p | OpenSquare q p} →
      ∀ p ∈ chosen, OpenSquare q (realPoint p) := by
    intro q hq hold
    have hq' : RowsContain w.after q := by simpa only [replaceRows,Function.update_same] using hq
    have hold' : rationalHull (prior i) ⊆ {p | OpenSquare q p} := by
      simpa only [replaceRows,hprior] using hold
    exact w.owned q hq' hold'
  obtain ⟨hprom,hown⟩ := promote_preserving_rowsOwn _ i chosen ho hv
  exact ⟨VerifiedTrace.cons hp (VerifiedTrace.cons hprom (VerifiedTrace.refl _)),hown⟩

theorem trace_trans {a b c : PoseState} (hab : VerifiedTrace a b) (hbc : VerifiedTrace b c) :
    VerifiedTrace a c := by
  induction hab generalizing c with
  | refl => exact hbc
  | cons hs ht ih => exact VerifiedTrace.cons hs (ih hbc)

end
end ElevenSquare.Pending.T03
