import ElevenSquare.Tasks.T02.FiniteSelfCuts
import ElevenSquare.Tasks.T02.FinitePruning

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- A recorded row first applies necessary self-hull cuts, then converts their
halfplane intersection to the recorded input polygon, and finally prunes it.
All three operations have explicit finite witnesses. The angular interval is
inherited from the actual predecessor row, not substituted by a receipt. -/
structure RowTransitionCertificate where
  selfCuts : List SelfHullCut
  domain : Polygon
  implications : List BaselineCombination
  pruning : RowPruningCertificate

def RowTransitionCertificate.inputRow (r : PoseRow) (c : RowTransitionCertificate) :
    PoseRow := { r with centers := c.domain }

def RowTransitionCertificate.Check (s : PoseState) (i : Owner) (r : PoseRow)
    (c : RowTransitionCertificate) : Prop :=
  (∀ cut ∈ c.selfCuts, cut.Check (s.owned i) r) ∧
  BaselinePolygonImplicationCheck (applySelfCuts (s.owned i) r c.selfCuts).centers
    c.domain c.implications ∧
  c.pruning.Check s i (c.inputRow r)

instance rowTransitionCertificateCheckDecidable (s : PoseState) (i : Owner)
    (r : PoseRow) (c : RowTransitionCertificate) :
    Decidable (c.Check s i r) := by
  unfold RowTransitionCertificate.Check
  infer_instance

def RowTransitionCertificate.outputRows (r : PoseRow) (c : RowTransitionCertificate) :
    List PoseRow := c.pruning.keptRows (c.inputRow r)

theorem row_transition_enters_input (s : PoseState) (i : Owner) (r : PoseRow)
    (c : RowTransitionCertificate) (hc : c.Check s i r) (q : UnitSquare)
    (hq : r.contains q) (ho : rationalHull (s.owned i) ⊆ {p | OpenSquare q p}) :
    (c.inputRow r).contains q := by
  have hcut := self_cut_row_keeps (s.owned i) r c.selfCuts hc.1 q hq ho
  exact ⟨baseline_polygon_implication_check_sound _ _ _ hc.2.1 hcut.1, hq.2⟩

/-- A row of an actual nonoverlapping packing survives in the checked retained
list. A forbidden alternative contradicts a distinct owner's strict hull. -/
theorem row_transition_keeps {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (i : Owner) (r : PoseRow) (c : RowTransitionCertificate)
    (hc : c.Check s i r) (hq : r.contains (P.squares i)) :
    RowsContain (c.outputRows r) (P.squares i) := by
  have hin := row_transition_enters_input s i r c hc _ hq (hs.2 i)
  rcases row_pruning_sound s i (c.inputRow r) c.pruning hc.2.2 _ hin with hkeep | hban
  · exact hkeep
  · obtain ⟨j, hij, Q, hcore, hforbidden⟩ := hban
    obtain ⟨p, hpi, hpj⟩ := forbidden_center_implies_overlap
      (P.squares i) (P.squares j) (rationalHull (s.owned j)) Q
      (hs.2 j) hcore hforbidden
    exact False.elim (P.interior_disjoint i j hij p ⟨hpi, hpj⟩)

def rowTransitionsOutput (plan : List (PoseRow × RowTransitionCertificate)) :
    List PoseRow := plan.bind (fun item => item.2.outputRows item.1)

theorem row_transitions_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (plan : List (PoseRow × RowTransitionCertificate))
    (hinput : plan.map Prod.fst = s.rows i)
    (hchecks : ∀ item ∈ plan, item.2.Check s i item.1) (hs : StateHolds P s) :
    StateHolds P (replaceRows s i (rowTransitionsOutput plan)) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases hji : j = i
  · subst j
    obtain ⟨r, hr, hq⟩ := hs.1 i
    rw [← hinput] at hr
    obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
    obtain ⟨out, hout, hcontains⟩ :=
      row_transition_keeps P s hs i item.1 item.2 (hchecks item hm) hq
    simp only [replaceRows, Function.update_same]
    exact ⟨out, List.mem_bind.mpr ⟨item, hm, hout⟩, hcontains⟩
  · simpa only [replaceRows, Function.update_noteq hji] using hs.1 j

end
end ElevenSquare.Tasks.T02
