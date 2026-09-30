import ElevenSquare.Pending.S05_Trace
import Mathlib.Tactic.Ring

/-! Combinators for assembling source-node certificates in bounded modules.
Each generated row obligation remains a geometric Lean proposition; the
combinators do not accept JSON status flags or Boolean replay results. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem verifiedTrace_trans {a b c : PoseState}
    (hab : VerifiedTrace a b) (hbc : VerifiedTrace b c) :
    VerifiedTrace a c := by
  induction hab with
  | refl _ => exact hbc
  | cons step _ ih => exact VerifiedTrace.cons step (ih hbc)

/-- Rowwise geometry lets a generator split a large `prunePosewise` step
across small proof modules while preserving its complete semantic cover. -/
theorem prunePosewise_of_row_certificates (s : PoseState) (i : Owner)
    (rs : List PoseRow)
    (hrows : ∀ r ∈ s.rows i, ∀ q : UnitSquare, r.contains q →
      RowsContain rs q ∨
        ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
          CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q) :
    VerifiedStep s (replaceRows s i rs) := by
  apply VerifiedStep.prunePosewise
  intro q hq
  obtain ⟨r, hr, hcontains⟩ := hq
  exact hrows r hr q hcontains

/-- A particularly small terminal checker: if each remaining pose contains
some point already owned by a different square, the whole owner's row list
can be removed. The witness and partner may vary with the pose. -/
theorem prune_all_by_owned_points (s : PoseState) (i : Owner)
    (hbad : ∀ q : UnitSquare, RowsContain (s.rows i) q →
      ∃ j : Owner, i ≠ j ∧ ∃ v ∈ s.owned j,
        OpenSquare q (realPoint v)) :
    VerifiedStep s (replaceRows s i []) := by
  apply VerifiedStep.prunePosewise
  intro q hq
  right
  obtain ⟨j, hij, v, hv, hinside⟩ := hbad q hq
  let w : Point := realPoint v
  refine ⟨j, hij, {w-q.center}, ?_, ?_⟩
  · intro u hu
    have heq : u = w-q.center := Set.mem_singleton_iff.mp hu
    subst u
    convert hinside using 1
    apply Prod.ext <;> dsimp [w] <;> ring
  · have hw : w ∈ rationalHull (s.owned j) :=
      subset_convexHull ℝ {p | ∃ v ∈ s.owned j, p = realPoint v}
        ⟨v, hv, rfl⟩
    refine ⟨w, hw, w-q.center, Set.mem_singleton _, ?_⟩
    apply Prod.ext <;> dsimp [w] <;> ring

/-- In a terminal node, only the rows for one owner need to be definitionally
empty; no enumeration of the other ten owners is necessary. -/
theorem terminal_of_empty_owner (s : PoseState) (i : Owner)
    (hempty : s.rows i = []) : Terminal s :=
  Or.inl ⟨i, hempty⟩

/-- A source-node certificate can be closed from its initial semantic state,
checked trace and terminal witness. -/
theorem terminal_trace_refutes {S : ℝ} (P : Packing 11 S)
    {a b : PoseState} (ha : StateHolds P a)
    (hab : VerifiedTrace a b) (hb : Terminal b) : False :=
  terminal_contradiction P b (verified_trace_sound P ha hab) hb

end
end ElevenSquare.Tasks.T07
