import ElevenSquare.Tasks.T02.RecordedProgram
import ElevenSquare.Tasks.T02.Prior1000Initialization.ArchivedRoot
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Complete
import ElevenSquare.Tasks.T02.Prior1000Step000Row000.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row001.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row002.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row003.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row004.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row005.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row006.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row007.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row008.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row009.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row010.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row011.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row012.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row013.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row014.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row015.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row016.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row017.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row018.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row019.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row020.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row021.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row022.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row023.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row024.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row025.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row026.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row027.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row028.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row029.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row030.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row031.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row032.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row033.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row034.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row035.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row036.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row037.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row038.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row039.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row040.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row041.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row042.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row043.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row044.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row045.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row046.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row047.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row048.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row049.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row050.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row051.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row052.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row053.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row054.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row055.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row056.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row057.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row058.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row059.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row060.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row061.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row062.TransitionChecks
import ElevenSquare.Tasks.T02.Prior1000Step000Row063.TransitionChecks

namespace ElevenSquare.Tasks.T02.Prior1000FirstStep
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

/-! Composition of the actual seed, all 64 closed-row updates, and the first
strict ownership promotion. This is one step, not a complete case exclusion. -/

def plan : List (PoseRow × RowTransitionCertificate) :=
  [(Prior1000Step000Row000.predecessorRow, Prior1000Step000Row000.transition),
   (Prior1000Step000Row001.predecessorRow, Prior1000Step000Row001.transition),
   (Prior1000Step000Row002.predecessorRow, Prior1000Step000Row002.transition),
   (Prior1000Step000Row003.predecessorRow, Prior1000Step000Row003.transition),
   (Prior1000Step000Row004.predecessorRow, Prior1000Step000Row004.transition),
   (Prior1000Step000Row005.predecessorRow, Prior1000Step000Row005.transition),
   (Prior1000Step000Row006.predecessorRow, Prior1000Step000Row006.transition),
   (Prior1000Step000Row007.predecessorRow, Prior1000Step000Row007.transition),
   (Prior1000Step000Row008.predecessorRow, Prior1000Step000Row008.transition),
   (Prior1000Step000Row009.predecessorRow, Prior1000Step000Row009.transition),
   (Prior1000Step000Row010.predecessorRow, Prior1000Step000Row010.transition),
   (Prior1000Step000Row011.predecessorRow, Prior1000Step000Row011.transition),
   (Prior1000Step000Row012.predecessorRow, Prior1000Step000Row012.transition),
   (Prior1000Step000Row013.predecessorRow, Prior1000Step000Row013.transition),
   (Prior1000Step000Row014.predecessorRow, Prior1000Step000Row014.transition),
   (Prior1000Step000Row015.predecessorRow, Prior1000Step000Row015.transition),
   (Prior1000Step000Row016.predecessorRow, Prior1000Step000Row016.transition),
   (Prior1000Step000Row017.predecessorRow, Prior1000Step000Row017.transition),
   (Prior1000Step000Row018.predecessorRow, Prior1000Step000Row018.transition),
   (Prior1000Step000Row019.predecessorRow, Prior1000Step000Row019.transition),
   (Prior1000Step000Row020.predecessorRow, Prior1000Step000Row020.transition),
   (Prior1000Step000Row021.predecessorRow, Prior1000Step000Row021.transition),
   (Prior1000Step000Row022.predecessorRow, Prior1000Step000Row022.transition),
   (Prior1000Step000Row023.predecessorRow, Prior1000Step000Row023.transition),
   (Prior1000Step000Row024.predecessorRow, Prior1000Step000Row024.transition),
   (Prior1000Step000Row025.predecessorRow, Prior1000Step000Row025.transition),
   (Prior1000Step000Row026.predecessorRow, Prior1000Step000Row026.transition),
   (Prior1000Step000Row027.predecessorRow, Prior1000Step000Row027.transition),
   (Prior1000Step000Row028.predecessorRow, Prior1000Step000Row028.transition),
   (Prior1000Step000Row029.predecessorRow, Prior1000Step000Row029.transition),
   (Prior1000Step000Row030.predecessorRow, Prior1000Step000Row030.transition),
   (Prior1000Step000Row031.predecessorRow, Prior1000Step000Row031.transition),
   (Prior1000Step000Row032.predecessorRow, Prior1000Step000Row032.transition),
   (Prior1000Step000Row033.predecessorRow, Prior1000Step000Row033.transition),
   (Prior1000Step000Row034.predecessorRow, Prior1000Step000Row034.transition),
   (Prior1000Step000Row035.predecessorRow, Prior1000Step000Row035.transition),
   (Prior1000Step000Row036.predecessorRow, Prior1000Step000Row036.transition),
   (Prior1000Step000Row037.predecessorRow, Prior1000Step000Row037.transition),
   (Prior1000Step000Row038.predecessorRow, Prior1000Step000Row038.transition),
   (Prior1000Step000Row039.predecessorRow, Prior1000Step000Row039.transition),
   (Prior1000Step000Row040.predecessorRow, Prior1000Step000Row040.transition),
   (Prior1000Step000Row041.predecessorRow, Prior1000Step000Row041.transition),
   (Prior1000Step000Row042.predecessorRow, Prior1000Step000Row042.transition),
   (Prior1000Step000Row043.predecessorRow, Prior1000Step000Row043.transition),
   (Prior1000Step000Row044.predecessorRow, Prior1000Step000Row044.transition),
   (Prior1000Step000Row045.predecessorRow, Prior1000Step000Row045.transition),
   (Prior1000Step000Row046.predecessorRow, Prior1000Step000Row046.transition),
   (Prior1000Step000Row047.predecessorRow, Prior1000Step000Row047.transition),
   (Prior1000Step000Row048.predecessorRow, Prior1000Step000Row048.transition),
   (Prior1000Step000Row049.predecessorRow, Prior1000Step000Row049.transition),
   (Prior1000Step000Row050.predecessorRow, Prior1000Step000Row050.transition),
   (Prior1000Step000Row051.predecessorRow, Prior1000Step000Row051.transition),
   (Prior1000Step000Row052.predecessorRow, Prior1000Step000Row052.transition),
   (Prior1000Step000Row053.predecessorRow, Prior1000Step000Row053.transition),
   (Prior1000Step000Row054.predecessorRow, Prior1000Step000Row054.transition),
   (Prior1000Step000Row055.predecessorRow, Prior1000Step000Row055.transition),
   (Prior1000Step000Row056.predecessorRow, Prior1000Step000Row056.transition),
   (Prior1000Step000Row057.predecessorRow, Prior1000Step000Row057.transition),
   (Prior1000Step000Row058.predecessorRow, Prior1000Step000Row058.transition),
   (Prior1000Step000Row059.predecessorRow, Prior1000Step000Row059.transition),
   (Prior1000Step000Row060.predecessorRow, Prior1000Step000Row060.transition),
   (Prior1000Step000Row061.predecessorRow, Prior1000Step000Row061.transition),
   (Prior1000Step000Row062.predecessorRow, Prior1000Step000Row062.transition),
   (Prior1000Step000Row063.predecessorRow, Prior1000Step000Row063.transition)]

theorem root_owned : Prior1000Initialization.archivedRoot.owned =
    Prior1000Step000Row000.ownedByRole := by
  funext i
  fin_cases i <;> rfl

theorem plan_input : plan.map Prod.fst =
    Prior1000Initialization.archivedRoot.rows (4 : Owner) := by
  change plan.map Prod.fst = Prior1000Initialization.Cell006.poseCertificate.rows
  simp only [plan, List.map_cons, List.map_nil, Prod.fst,
Prior1000Step000Row000.predecessor_matches_seed,
    Prior1000Step000Row001.predecessor_matches_seed,
    Prior1000Step000Row002.predecessor_matches_seed,
    Prior1000Step000Row003.predecessor_matches_seed,
    Prior1000Step000Row004.predecessor_matches_seed,
    Prior1000Step000Row005.predecessor_matches_seed,
    Prior1000Step000Row006.predecessor_matches_seed,
    Prior1000Step000Row007.predecessor_matches_seed,
    Prior1000Step000Row008.predecessor_matches_seed,
    Prior1000Step000Row009.predecessor_matches_seed,
    Prior1000Step000Row010.predecessor_matches_seed,
    Prior1000Step000Row011.predecessor_matches_seed,
    Prior1000Step000Row012.predecessor_matches_seed,
    Prior1000Step000Row013.predecessor_matches_seed,
    Prior1000Step000Row014.predecessor_matches_seed,
    Prior1000Step000Row015.predecessor_matches_seed,
    Prior1000Step000Row016.predecessor_matches_seed,
    Prior1000Step000Row017.predecessor_matches_seed,
    Prior1000Step000Row018.predecessor_matches_seed,
    Prior1000Step000Row019.predecessor_matches_seed,
    Prior1000Step000Row020.predecessor_matches_seed,
    Prior1000Step000Row021.predecessor_matches_seed,
    Prior1000Step000Row022.predecessor_matches_seed,
    Prior1000Step000Row023.predecessor_matches_seed,
    Prior1000Step000Row024.predecessor_matches_seed,
    Prior1000Step000Row025.predecessor_matches_seed,
    Prior1000Step000Row026.predecessor_matches_seed,
    Prior1000Step000Row027.predecessor_matches_seed,
    Prior1000Step000Row028.predecessor_matches_seed,
    Prior1000Step000Row029.predecessor_matches_seed,
    Prior1000Step000Row030.predecessor_matches_seed,
    Prior1000Step000Row031.predecessor_matches_seed,
    Prior1000Step000Row032.predecessor_matches_seed,
    Prior1000Step000Row033.predecessor_matches_seed,
    Prior1000Step000Row034.predecessor_matches_seed,
    Prior1000Step000Row035.predecessor_matches_seed,
    Prior1000Step000Row036.predecessor_matches_seed,
    Prior1000Step000Row037.predecessor_matches_seed,
    Prior1000Step000Row038.predecessor_matches_seed,
    Prior1000Step000Row039.predecessor_matches_seed,
    Prior1000Step000Row040.predecessor_matches_seed,
    Prior1000Step000Row041.predecessor_matches_seed,
    Prior1000Step000Row042.predecessor_matches_seed,
    Prior1000Step000Row043.predecessor_matches_seed,
    Prior1000Step000Row044.predecessor_matches_seed,
    Prior1000Step000Row045.predecessor_matches_seed,
    Prior1000Step000Row046.predecessor_matches_seed,
    Prior1000Step000Row047.predecessor_matches_seed,
    Prior1000Step000Row048.predecessor_matches_seed,
    Prior1000Step000Row049.predecessor_matches_seed,
    Prior1000Step000Row050.predecessor_matches_seed,
    Prior1000Step000Row051.predecessor_matches_seed,
    Prior1000Step000Row052.predecessor_matches_seed,
    Prior1000Step000Row053.predecessor_matches_seed,
    Prior1000Step000Row054.predecessor_matches_seed,
    Prior1000Step000Row055.predecessor_matches_seed,
    Prior1000Step000Row056.predecessor_matches_seed,
    Prior1000Step000Row057.predecessor_matches_seed,
    Prior1000Step000Row058.predecessor_matches_seed,
    Prior1000Step000Row059.predecessor_matches_seed,
    Prior1000Step000Row060.predecessor_matches_seed,
    Prior1000Step000Row061.predecessor_matches_seed,
    Prior1000Step000Row062.predecessor_matches_seed,
    Prior1000Step000Row063.predecessor_matches_seed]
  rfl

theorem plan_output : rowTransitionsOutput plan =
    Prior1000Step000Ownership.retainedRows := by
  rfl

def prunedState : PoseState := replaceRows Prior1000Initialization.archivedRoot
  (4 : Owner) Prior1000Step000Ownership.retainedRows

def nextState : PoseState := replaceHull prunedState (4 : Owner)
  Prior1000Step000Ownership.nextOwned

def program : List RecordedInstruction :=
  [.rows (4 : Owner) plan,
   .basic (.trace (.ownership (4 : Owner) Prior1000Step000Ownership.ownershipCertificate))]

theorem program_output : recordedProgramRun
    Prior1000Initialization.archivedRoot program = nextState := by
  rfl


end
end ElevenSquare.Tasks.T02.Prior1000FirstStep
