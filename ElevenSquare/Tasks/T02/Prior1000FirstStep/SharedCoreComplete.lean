import ElevenSquare.Tasks.T02.Prior1000FirstStep.Plan
import ElevenSquare.Tasks.T02.Prior1000Step000Row000.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row001.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row002.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row003.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row004.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row005.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row006.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row007.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row008.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row009.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row010.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row011.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row012.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row013.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row014.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row015.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row016.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row017.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row018.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row019.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row020.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row021.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row022.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row023.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row024.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row025.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row026.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row027.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row028.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row029.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row030.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row031.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row032.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row033.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row034.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row035.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row036.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row037.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row038.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row039.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row040.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row041.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row042.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row043.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row044.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row045.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row046.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row047.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row048.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row049.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row050.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row051.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row052.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row053.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row054.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row055.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row056.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row057.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row058.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row059.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row060.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row061.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row062.SharedCoreInteger.Transition
import ElevenSquare.Tasks.T02.Prior1000Step000Row063.SharedCoreInteger.Transition

namespace ElevenSquare.Tasks.T02.Prior1000FirstStep.SharedCore
open ElevenSquare.Pending ElevenSquare.Tasks.T02 ElevenSquare.Tasks.T02.Prior1000FirstStep
noncomputable section
set_option maxRecDepth 100000

theorem mixed_plan_checked : ∀ item ∈ plan,
    item.2.Check Prior1000Initialization.archivedRoot (4 : Owner) item.1 ∨
      ∃ cover, IntegerTransitionCheck Prior1000Initialization.archivedRoot
        (4 : Owner) item.1 item.2 cover := by
  intro item hm
  simp only [plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right
    exact ⟨Prior1000Step000Row000.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row000.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row001.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row001.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row002.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row002.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row003.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row003.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row004.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row004.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row005.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row005.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row006.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row006.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row007.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row007.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row008.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row008.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row009.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row009.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row010.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row010.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row011.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row011.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row012.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row012.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row013.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row013.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row014.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row014.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row015.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row015.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row016.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row016.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row017.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row017.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row018.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row018.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row019.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row019.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row020.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row020.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row021.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row021.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row022.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row022.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row023.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row023.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row024.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row024.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row025.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row025.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row026.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row026.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row027.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row027.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row028.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row028.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row029.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row029.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row030.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row030.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row031.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row031.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row032.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row032.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row033.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row033.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row034.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row034.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row035.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row035.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row036.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row036.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row037.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row037.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row038.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row038.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row039.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row039.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row040.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row040.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row041.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row041.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row042.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row042.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row043.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row043.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row044.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row044.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row045.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row045.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row046.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row046.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row047.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row047.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row048.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row048.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row049.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row049.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row050.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row050.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row051.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row051.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row052.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row052.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row053.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row053.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row054.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row054.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row055.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row055.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row056.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row056.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row057.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row057.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row058.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row058.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row059.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row059.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row060.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row060.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row061.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row061.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row062.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row062.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩
  · right
    exact ⟨Prior1000Step000Row063.SharedCoreInteger.integerCertificate,
      Prior1000Step000Row063.SharedCoreInteger.transition_checked_of_owned _ root_owned⟩

theorem integer_pruned_state_holds {S : ℝ} (P : Packing 11 S)
    (hs : StateHolds P Prior1000Initialization.archivedRoot) : StateHolds P prunedState := by
  have h := mixed_row_transitions_sound P Prior1000Initialization.archivedRoot
    (4 : Owner) plan plan_input mixed_plan_checked hs
  simpa only [plan_output, prunedState] using h

theorem integer_first_step_holds {S : ℝ} (P : Packing 11 S)
    (hs : StateHolds P Prior1000Initialization.archivedRoot) : StateHolds P nextState := by
  apply Prior1000Step000Ownership.packing_promotion_holds P prunedState
    (integer_pruned_state_holds P hs)
  · simp only [prunedState, replaceRows, Function.update_self]
  · rfl

theorem case1000_after_integer_first_step (P : Packing 11 coverCap)
    (hc : IsCharted P) (ho : Occupies P (caseMask 1000)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) nextState := by
  obtain ⟨perm, hs⟩ := Prior1000Initialization.case1000_initialized P hc ho
  exact ⟨perm, integer_first_step_holds _ hs⟩

end
end ElevenSquare.Tasks.T02.Prior1000FirstStep.SharedCore
