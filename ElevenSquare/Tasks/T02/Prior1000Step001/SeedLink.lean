import ElevenSquare.Tasks.T02.Prior1000Step001.Complete
import ElevenSquare.Tasks.T02.Prior1000Step001Row000.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row001.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row002.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row003.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row004.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row005.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row006.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row007.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row008.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row009.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row010.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row011.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row012.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row013.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row014.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row015.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row016.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row017.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row018.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row019.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row020.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row021.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row022.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row023.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row024.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row025.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row026.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row027.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row028.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row029.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row030.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row031.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row032.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row033.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row034.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row035.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row036.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row037.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row038.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row039.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row040.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row041.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row042.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row043.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row044.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row045.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row046.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row047.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row048.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row049.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row050.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row051.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row052.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row053.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row054.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row055.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row056.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row057.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row058.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row059.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row060.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row061.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row062.Predecessor
import ElevenSquare.Tasks.T02.Prior1000Step001Row063.Predecessor

namespace ElevenSquare.Tasks.T02.Prior1000Step001
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

/-- The proposed second-step inputs are exactly the untouched initial cell-9
rows, not merely samples or boxes containing those rows. -/
theorem predecessor_rows_eq_seed :
    predecessorRows = Prior1000Initialization.Cell009.poseCertificate.rows := by
  simp only [predecessorRows, records, List.map_cons, List.map_nil,
    IntegerRowRecord.predecessor,
    Prior1000Step001Row000.predecessor_matches_seed,
    Prior1000Step001Row001.predecessor_matches_seed,
    Prior1000Step001Row002.predecessor_matches_seed,
    Prior1000Step001Row003.predecessor_matches_seed,
    Prior1000Step001Row004.predecessor_matches_seed,
    Prior1000Step001Row005.predecessor_matches_seed,
    Prior1000Step001Row006.predecessor_matches_seed,
    Prior1000Step001Row007.predecessor_matches_seed,
    Prior1000Step001Row008.predecessor_matches_seed,
    Prior1000Step001Row009.predecessor_matches_seed,
    Prior1000Step001Row010.predecessor_matches_seed,
    Prior1000Step001Row011.predecessor_matches_seed,
    Prior1000Step001Row012.predecessor_matches_seed,
    Prior1000Step001Row013.predecessor_matches_seed,
    Prior1000Step001Row014.predecessor_matches_seed,
    Prior1000Step001Row015.predecessor_matches_seed,
    Prior1000Step001Row016.predecessor_matches_seed,
    Prior1000Step001Row017.predecessor_matches_seed,
    Prior1000Step001Row018.predecessor_matches_seed,
    Prior1000Step001Row019.predecessor_matches_seed,
    Prior1000Step001Row020.predecessor_matches_seed,
    Prior1000Step001Row021.predecessor_matches_seed,
    Prior1000Step001Row022.predecessor_matches_seed,
    Prior1000Step001Row023.predecessor_matches_seed,
    Prior1000Step001Row024.predecessor_matches_seed,
    Prior1000Step001Row025.predecessor_matches_seed,
    Prior1000Step001Row026.predecessor_matches_seed,
    Prior1000Step001Row027.predecessor_matches_seed,
    Prior1000Step001Row028.predecessor_matches_seed,
    Prior1000Step001Row029.predecessor_matches_seed,
    Prior1000Step001Row030.predecessor_matches_seed,
    Prior1000Step001Row031.predecessor_matches_seed,
    Prior1000Step001Row032.predecessor_matches_seed,
    Prior1000Step001Row033.predecessor_matches_seed,
    Prior1000Step001Row034.predecessor_matches_seed,
    Prior1000Step001Row035.predecessor_matches_seed,
    Prior1000Step001Row036.predecessor_matches_seed,
    Prior1000Step001Row037.predecessor_matches_seed,
    Prior1000Step001Row038.predecessor_matches_seed,
    Prior1000Step001Row039.predecessor_matches_seed,
    Prior1000Step001Row040.predecessor_matches_seed,
    Prior1000Step001Row041.predecessor_matches_seed,
    Prior1000Step001Row042.predecessor_matches_seed,
    Prior1000Step001Row043.predecessor_matches_seed,
    Prior1000Step001Row044.predecessor_matches_seed,
    Prior1000Step001Row045.predecessor_matches_seed,
    Prior1000Step001Row046.predecessor_matches_seed,
    Prior1000Step001Row047.predecessor_matches_seed,
    Prior1000Step001Row048.predecessor_matches_seed,
    Prior1000Step001Row049.predecessor_matches_seed,
    Prior1000Step001Row050.predecessor_matches_seed,
    Prior1000Step001Row051.predecessor_matches_seed,
    Prior1000Step001Row052.predecessor_matches_seed,
    Prior1000Step001Row053.predecessor_matches_seed,
    Prior1000Step001Row054.predecessor_matches_seed,
    Prior1000Step001Row055.predecessor_matches_seed,
    Prior1000Step001Row056.predecessor_matches_seed,
    Prior1000Step001Row057.predecessor_matches_seed,
    Prior1000Step001Row058.predecessor_matches_seed,
    Prior1000Step001Row059.predecessor_matches_seed,
    Prior1000Step001Row060.predecessor_matches_seed,
    Prior1000Step001Row061.predecessor_matches_seed,
    Prior1000Step001Row062.predecessor_matches_seed,
    Prior1000Step001Row063.predecessor_matches_seed]
  rfl

end
end ElevenSquare.Tasks.T02.Prior1000Step001
