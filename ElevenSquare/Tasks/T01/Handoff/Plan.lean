import ElevenSquare.Tasks.T01.StateProgram
import ElevenSquare.Tasks.T01.CenterCuts
import ElevenSquare.Tasks.T01.FiniteMajority
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.Universal
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.GroupedProgram
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MixedFeature
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.WeightedField
import ElevenSquare.Cases
import ElevenSquare.Orientation

namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section

/-- Raw finite witnesses only. No proof fields, hidden premises, or external oracle. -/
inductive Plan where
  | terminal (certificate : TerminalCertificate)
  | steps (program : List StateInstruction) (rest : Plan)
  | universalSteps (owner : Owner)
      (program : List (PoseRow × PlanAPI.UniversalRowPruningCertificate)) (rest : Plan)
  | groupedUniversalSteps (owner : Owner)
      (program : List (PoseRow × PlanAPI.GroupedRowPruningCertificate)) (rest : Plan)
  | split (owner : Owner) (halfplane : Halfplane) (left right : Plan)
  | majority (sites : Finset QPoint) (threshold : ℕ) (left right : Owner)
      (leftRows rightRows : List (PoseRow × MajorityRowPlan))
  | mixed (certificate : PlanAPI.MixedThreePlan)
  | weighted {n : ℕ} (certificate : PlanAPI.WeightedFieldPlan n)

/-- Exact finite checks, including row identities and complete finite covers.
These are not all analytic inequalities: do not drop the combinatorial checks. -/
def Plan.ProgramChecks (s : PoseState) : Plan → Prop
  | .terminal _ => True
  | .steps p rest => StateProgramCheck s p ∧ rest.ProgramChecks (stateProgramRun s p)
  | .universalSteps i p rest =>
      PlanAPI.UniversalProgramCheck s i p ∧
        rest.ProgramChecks (replaceRows s i (PlanAPI.universalProgramOutput p))
  | .groupedUniversalSteps i p rest =>
      PlanAPI.GroupedProgramCheck s i p ∧
        rest.ProgramChecks (replaceRows s i (PlanAPI.groupedProgramOutput p))
  | .split i h left right =>
      left.ProgramChecks (centerCut s i h) ∧
      right.ProgramChecks (centerCut s i (baselineFlip h))
  | .majority sites n i j li lj =>
      li.map Prod.fst = s.rows i ∧ lj.map Prod.fst = s.rows j ∧
      (∀ item ∈ li, MajorityRowCheck sites n s i item.1 item.2) ∧
      (∀ item ∈ lj, MajorityRowCheck sites n s j item.1 item.2)
  | .mixed c => c.Check s
  | .weighted c => c.Check s

def Plan.LeafChecks (s : PoseState) : Plan → Prop
  | .terminal c => c.Check s
  | .steps p rest => rest.LeafChecks (stateProgramRun s p)
  | .universalSteps i p rest =>
      rest.LeafChecks (replaceRows s i (PlanAPI.universalProgramOutput p))
  | .groupedUniversalSteps i p rest =>
      rest.LeafChecks (replaceRows s i (PlanAPI.groupedProgramOutput p))
  | .split i h left right =>
      left.LeafChecks (centerCut s i h) ∧
      right.LeafChecks (centerCut s i (baselineFlip h))
  | .majority sites n i j _ _ => sites.card + 1 = 2 * n ∧ i ≠ j
  | .mixed _ => True
  | .weighted _ => True

theorem plan_sound {S : ℝ} (P : Packing 11 S) (p : Plan) (s : PoseState)
    (hp : p.ProgramChecks s) (hl : p.LeafChecks s) (hs : StateHolds P s) : False := by
  induction p generalizing s with
  | terminal c =>
    exact terminal_contradiction P s hs (terminal_certificate_sound s c hl)
  | steps program rest ih =>
    exact ih _ hp.2 hl (state_program_sound P s program hp.1 hs)
  | universalSteps i program rest ih =>
    exact ih _ hp.2 hl (PlanAPI.universal_program_sound P s i program hp.1 hs)
  | groupedUniversalSteps i program rest ih =>
    exact ih _ hp.2 hl (PlanAPI.grouped_program_sound P s i program hp.1 hs)
  | split i h left right ihl ihr =>
    rcases centerCut_cover P s i h hs with hleft | hright
    · exact ihl _ hp.1 hl.1 hleft
    · exact ihr _ hp.2 hl.2 hright
  | majority sites n i j li lj =>
    exact hl.2 (baseline_majority_unique_owner P sites n hl.1 i j
      (majority_owner_checked P s hs sites n i li hp.1 hp.2.2.1)
      (majority_owner_checked P s hs sites n j lj hp.2.1 hp.2.2.2))
  | mixed c =>
    exact PlanAPI.mixed_three_plan_refutes P s c hp hs
  | weighted c =>
    exact PlanAPI.weighted_field_plan_refutes P s c hp hs

def RootValid (m : Finset (Fin 16)) (root : PoseState) : Prop :=
  ∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) root

def emptyState : PoseState where
  rows := fun _ => []
  owned := fun _ => []

/-- Once an actual initialized plan refutes the packing, this adapts it to
the frozen linear-trace contract. Its empty root follows by contradiction;
it cannot bypass any initialization or plan-check obligation. -/
theorem certificate_of_plan (m : Finset (Fin 16)) (root : PoseState) (p : Plan)
    (hr : RootValid m root) (hp : p.ProgramChecks root) (hl : p.LeafChecks root) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨emptyState, emptyState, ?_, VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P hc ho
  obtain ⟨perm, hs⟩ := hr P hc ho
  exact False.elim (plan_sound (relabelPacking P perm) p root hp hl hs)

end
end ElevenSquare.Tasks.T01.Handoff
