import ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot
import ElevenSquare.Tasks.T01.SharedFieldOwnership.Complete
import Mathlib.Data.Bool.AllAny

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.SharedFieldOwnership
noncomputable section

/-- Every archived initial hull vertex for G070 appears among the checked
    shared field ownership points for the corresponding physical cell. -/
theorem ownedAt_subset_sharedRoster (i : Owner) :
    ∀ p ∈ G070.ownedAt i, p ∈ sharedRoster (G070.physicalCell i) := by
  have hcheck :
      (G070.ownedAt i).all
        (fun p => p ∈ sharedRoster (G070.physicalCell i)) = true := by
    fin_cases i
    · change (G070.owned00).all (fun p => p ∈ sharedRosterCell01) = true
      norm_num [G070.owned00, sharedRosterCell01]
    · change (G070.owned01).all (fun p => p ∈ sharedRosterCell02) = true
      norm_num [G070.owned01, sharedRosterCell02]
    · change (G070.owned02).all (fun p => p ∈ sharedRosterCell03) = true
      norm_num [G070.owned02, sharedRosterCell03]
    · change (G070.owned03).all (fun p => p ∈ sharedRosterCell05) = true
      norm_num [G070.owned03, sharedRosterCell05]
    · change (G070.owned04).all (fun p => p ∈ sharedRosterCell06) = true
      norm_num [G070.owned04, sharedRosterCell06]
    · change (G070.owned05).all (fun p => p ∈ sharedRosterCell07) = true
      norm_num [G070.owned05, sharedRosterCell07]
    · change (G070.owned06).all (fun p => p ∈ sharedRosterCell09) = true
      norm_num [G070.owned06, sharedRosterCell09]
    · change (G070.owned07).all (fun p => p ∈ sharedRosterCell10) = true
      norm_num [G070.owned07, sharedRosterCell10]
    · change (G070.owned08).all (fun p => p ∈ sharedRosterCell11) = true
      norm_num [G070.owned08, sharedRosterCell11]
    · change (G070.owned09).all (fun p => p ∈ sharedRosterCell12) = true
      norm_num [G070.owned09, sharedRosterCell12]
    · change (G070.owned10).all (fun p => p ∈ sharedRosterCell14) = true
      norm_num [G070.owned10, sharedRosterCell14]
  exact List.all_iff_forall_prop.mp hcheck

/-- Unconditional kernel-checked initialization of the G070 state, with the
    terminal owner already represented by eight wider pose bins. -/
theorem terminal_coarse_initialized :
    RootValid G070.mask terminalCoarseRoot := by
  apply terminal_coarse_initialized_of_pointwise_ownership
  intro i q hcell hcont hchart p hp
  exact shared_roster_full_chart (G070.physicalCell i) q hcell hcont hchart
    p (ownedAt_subset_sharedRoster i p hp)

theorem initialized : RootValid G070.mask root := by
  apply initialized_of_pointwise_ownership
  intro i q hcell hcont hchart p hp
  exact shared_roster_full_chart (G070.physicalCell i) q hcell hcont hchart
    p (ownedAt_subset_sharedRoster i p hp)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot.ownedAt_subset_sharedRoster
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot.terminal_coarse_initialized
