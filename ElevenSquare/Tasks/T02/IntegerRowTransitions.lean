import ElevenSquare.Tasks.T02.IntegerPruning
import ElevenSquare.Tasks.T02.RowTransitions

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- Alternate finite verification of an existing row transition. The retained
rows and the actual predecessor stay exactly those of the original record. -/
def IntegerTransitionCheck (s : PoseState) (i : Owner) (r : PoseRow)
    (c : RowTransitionCertificate) (cover : IntegerCover.RationalCertificate) : Prop :=
  (∀ cut ∈ c.selfCuts, cut.Check (s.owned i) r) ∧
  BaselinePolygonImplicationCheck (applySelfCuts (s.owned i) r c.selfCuts).centers
    c.domain c.implications ∧
  cover.Check c.domain c.pruning.targets ∧
  ∀ piece ∈ c.pruning.forbidden, piece.Check s i (c.inputRow r)

instance (s : PoseState) (i : Owner) (r : PoseRow)
    (c : RowTransitionCertificate) (cover : IntegerCover.RationalCertificate) :
    Decidable (IntegerTransitionCheck s i r c cover) := by
  unfold IntegerTransitionCheck
  infer_instance

theorem integer_row_transition_keeps {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (i : Owner) (r : PoseRow) (c : RowTransitionCertificate)
    (cover : IntegerCover.RationalCertificate)
    (hc : IntegerTransitionCheck s i r c cover) (hq : r.contains (P.squares i)) :
    RowsContain (c.outputRows r) (P.squares i) := by
  have hcut := self_cut_row_keeps (s.owned i) r c.selfCuts hc.1 _ hq (hs.2 i)
  have hin : (c.inputRow r).contains (P.squares i) :=
    ⟨baseline_polygon_implication_check_sound _ _ _ hc.2.1 hcut.1, hq.2⟩
  rcases integer_row_pruning_sound s i (c.inputRow r) c.pruning cover
      hc.2.2.1 hc.2.2.2 _ hin with hkeep | hban
  · exact hkeep
  · obtain ⟨j, hij, Q, hcore, hforbidden⟩ := hban
    obtain ⟨p, hpi, hpj⟩ := forbidden_center_implies_overlap
      (P.squares i) (P.squares j) (rationalHull (s.owned j)) Q
      (hs.2 j) hcore hforbidden
    exact False.elim (P.interior_disjoint i j hij p ⟨hpi, hpj⟩)

/-- Mixed old/new verification is permitted row by row. In either alternative,
the same exact transition and output state are checked. -/
theorem mixed_row_transitions_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (plan : List (PoseRow × RowTransitionCertificate))
    (hinput : plan.map Prod.fst = s.rows i)
    (hchecks : ∀ item ∈ plan, item.2.Check s i item.1 ∨
      ∃ cover, IntegerTransitionCheck s i item.1 item.2 cover)
    (hs : StateHolds P s) :
    StateHolds P (replaceRows s i (rowTransitionsOutput plan)) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases hji : j = i
  · subst j
    obtain ⟨r, hr, hq⟩ := hs.1 i
    rw [← hinput] at hr
    obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
    have hout : RowsContain (item.2.outputRows item.1) (P.squares i) := by
      rcases hchecks item hm with old | ⟨cover, new⟩
      · exact row_transition_keeps P s hs i item.1 item.2 old hq
      · exact integer_row_transition_keeps P s hs i item.1 item.2 cover new hq
    obtain ⟨out, hout, hcontains⟩ := hout
    simp only [replaceRows, Function.update_same]
    exact ⟨out, List.mem_bind.mpr ⟨item, hm, hout⟩, hcontains⟩
  · simpa only [replaceRows, Function.update_noteq hji] using hs.1 j

end
end ElevenSquare.Tasks.T02
