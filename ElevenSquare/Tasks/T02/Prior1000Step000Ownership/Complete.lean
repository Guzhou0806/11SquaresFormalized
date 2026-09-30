import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row000.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row001.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row002.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row003.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row004.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row005.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row006.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row007.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row008.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row009.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row010.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row011.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row012.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row013.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row014.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row015.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row016.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row017.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row018.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row019.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row020.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row021.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row022.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row023.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row024.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row025.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row026.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row027.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row028.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row029.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row030.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row031.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row032.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row033.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row034.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row035.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row036.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row037.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row038.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row039.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row040.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row041.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row042.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row043.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row044.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row045.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row046.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row047.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row048.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row049.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row050.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row051.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row052.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row053.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row054.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row055.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row056.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row057.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row058.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row059.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row060.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row061.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row062.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row063.Checks

namespace ElevenSquare.Tasks.T02.Prior1000Step000Ownership
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

set_option maxRecDepth 100000

def retainedRows : List PoseRow :=
  [Row000.retainedRow,
   Row001.retainedRow,
   Row002.retainedRow,
   Row003.retainedRow,
   Row004.retainedRow,
   Row005.retainedRow,
   Row006.retainedRow,
   Row007.retainedRow,
   Row008.retainedRow,
   Row009.retainedRow,
   Row010.retainedRow,
   Row011.retainedRow,
   Row012.retainedRow,
   Row013.retainedRow,
   Row014.retainedRow,
   Row015.retainedRow,
   Row016.retainedRow,
   Row017.retainedRow,
   Row018.retainedRow,
   Row019.retainedRow,
   Row020.retainedRow,
   Row021.retainedRow,
   Row022.retainedRow,
   Row023.retainedRow,
   Row024.retainedRow,
   Row025.retainedRow,
   Row026.retainedRow,
   Row027.retainedRow,
   Row028.retainedRow,
   Row029.retainedRow,
   Row030.retainedRow,
   Row031.retainedRow,
   Row032.retainedRow,
   Row033.retainedRow,
   Row034.retainedRow,
   Row035.retainedRow,
   Row036.retainedRow,
   Row037.retainedRow,
   Row038.retainedRow,
   Row039.retainedRow,
   Row040.retainedRow,
   Row041.retainedRow,
   Row042.retainedRow,
   Row043.retainedRow,
   Row044.retainedRow,
   Row045.retainedRow,
   Row046.retainedRow,
   Row047.retainedRow,
   Row048.retainedRow,
   Row049.retainedRow,
   Row050.retainedRow,
   Row051.retainedRow,
   Row052.retainedRow,
   Row053.retainedRow,
   Row054.retainedRow,
   Row055.retainedRow,
   Row056.retainedRow,
   Row057.retainedRow,
   Row058.retainedRow,
   Row059.retainedRow,
   Row060.retainedRow,
   Row061.retainedRow,
   Row062.retainedRow,
   Row063.retainedRow]

def checkedRows : List (PoseRow × List QPoint) :=
  [(Row000.retainedRow, Row000.retainedVertices),
   (Row001.retainedRow, Row001.retainedVertices),
   (Row002.retainedRow, Row002.retainedVertices),
   (Row003.retainedRow, Row003.retainedVertices),
   (Row004.retainedRow, Row004.retainedVertices),
   (Row005.retainedRow, Row005.retainedVertices),
   (Row006.retainedRow, Row006.retainedVertices),
   (Row007.retainedRow, Row007.retainedVertices),
   (Row008.retainedRow, Row008.retainedVertices),
   (Row009.retainedRow, Row009.retainedVertices),
   (Row010.retainedRow, Row010.retainedVertices),
   (Row011.retainedRow, Row011.retainedVertices),
   (Row012.retainedRow, Row012.retainedVertices),
   (Row013.retainedRow, Row013.retainedVertices),
   (Row014.retainedRow, Row014.retainedVertices),
   (Row015.retainedRow, Row015.retainedVertices),
   (Row016.retainedRow, Row016.retainedVertices),
   (Row017.retainedRow, Row017.retainedVertices),
   (Row018.retainedRow, Row018.retainedVertices),
   (Row019.retainedRow, Row019.retainedVertices),
   (Row020.retainedRow, Row020.retainedVertices),
   (Row021.retainedRow, Row021.retainedVertices),
   (Row022.retainedRow, Row022.retainedVertices),
   (Row023.retainedRow, Row023.retainedVertices),
   (Row024.retainedRow, Row024.retainedVertices),
   (Row025.retainedRow, Row025.retainedVertices),
   (Row026.retainedRow, Row026.retainedVertices),
   (Row027.retainedRow, Row027.retainedVertices),
   (Row028.retainedRow, Row028.retainedVertices),
   (Row029.retainedRow, Row029.retainedVertices),
   (Row030.retainedRow, Row030.retainedVertices),
   (Row031.retainedRow, Row031.retainedVertices),
   (Row032.retainedRow, Row032.retainedVertices),
   (Row033.retainedRow, Row033.retainedVertices),
   (Row034.retainedRow, Row034.retainedVertices),
   (Row035.retainedRow, Row035.retainedVertices),
   (Row036.retainedRow, Row036.retainedVertices),
   (Row037.retainedRow, Row037.retainedVertices),
   (Row038.retainedRow, Row038.retainedVertices),
   (Row039.retainedRow, Row039.retainedVertices),
   (Row040.retainedRow, Row040.retainedVertices),
   (Row041.retainedRow, Row041.retainedVertices),
   (Row042.retainedRow, Row042.retainedVertices),
   (Row043.retainedRow, Row043.retainedVertices),
   (Row044.retainedRow, Row044.retainedVertices),
   (Row045.retainedRow, Row045.retainedVertices),
   (Row046.retainedRow, Row046.retainedVertices),
   (Row047.retainedRow, Row047.retainedVertices),
   (Row048.retainedRow, Row048.retainedVertices),
   (Row049.retainedRow, Row049.retainedVertices),
   (Row050.retainedRow, Row050.retainedVertices),
   (Row051.retainedRow, Row051.retainedVertices),
   (Row052.retainedRow, Row052.retainedVertices),
   (Row053.retainedRow, Row053.retainedVertices),
   (Row054.retainedRow, Row054.retainedVertices),
   (Row055.retainedRow, Row055.retainedVertices),
   (Row056.retainedRow, Row056.retainedVertices),
   (Row057.retainedRow, Row057.retainedVertices),
   (Row058.retainedRow, Row058.retainedVertices),
   (Row059.retainedRow, Row059.retainedVertices),
   (Row060.retainedRow, Row060.retainedVertices),
   (Row061.retainedRow, Row061.retainedVertices),
   (Row062.retainedRow, Row062.retainedVertices),
   (Row063.retainedRow, Row063.retainedVertices)]

def ownershipCertificate : OwnershipCertificate :=
  ⟨freshVertices, nextOwned, checkedRows, nextWitnesses⟩

theorem all_rows_points_checked : ∀ item ∈ checkedRows, ∀ p ∈ freshVertices,
    DirectPointCheck item.1 item.2 p := by
  intro item hi
  simp only [checkedRows, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Row000.promoted_points_checked
  · exact Row001.promoted_points_checked
  · exact Row002.promoted_points_checked
  · exact Row003.promoted_points_checked
  · exact Row004.promoted_points_checked
  · exact Row005.promoted_points_checked
  · exact Row006.promoted_points_checked
  · exact Row007.promoted_points_checked
  · exact Row008.promoted_points_checked
  · exact Row009.promoted_points_checked
  · exact Row010.promoted_points_checked
  · exact Row011.promoted_points_checked
  · exact Row012.promoted_points_checked
  · exact Row013.promoted_points_checked
  · exact Row014.promoted_points_checked
  · exact Row015.promoted_points_checked
  · exact Row016.promoted_points_checked
  · exact Row017.promoted_points_checked
  · exact Row018.promoted_points_checked
  · exact Row019.promoted_points_checked
  · exact Row020.promoted_points_checked
  · exact Row021.promoted_points_checked
  · exact Row022.promoted_points_checked
  · exact Row023.promoted_points_checked
  · exact Row024.promoted_points_checked
  · exact Row025.promoted_points_checked
  · exact Row026.promoted_points_checked
  · exact Row027.promoted_points_checked
  · exact Row028.promoted_points_checked
  · exact Row029.promoted_points_checked
  · exact Row030.promoted_points_checked
  · exact Row031.promoted_points_checked
  · exact Row032.promoted_points_checked
  · exact Row033.promoted_points_checked
  · exact Row034.promoted_points_checked
  · exact Row035.promoted_points_checked
  · exact Row036.promoted_points_checked
  · exact Row037.promoted_points_checked
  · exact Row038.promoted_points_checked
  · exact Row039.promoted_points_checked
  · exact Row040.promoted_points_checked
  · exact Row041.promoted_points_checked
  · exact Row042.promoted_points_checked
  · exact Row043.promoted_points_checked
  · exact Row044.promoted_points_checked
  · exact Row045.promoted_points_checked
  · exact Row046.promoted_points_checked
  · exact Row047.promoted_points_checked
  · exact Row048.promoted_points_checked
  · exact Row049.promoted_points_checked
  · exact Row050.promoted_points_checked
  · exact Row051.promoted_points_checked
  · exact Row052.promoted_points_checked
  · exact Row053.promoted_points_checked
  · exact Row054.promoted_points_checked
  · exact Row055.promoted_points_checked
  · exact Row056.promoted_points_checked
  · exact Row057.promoted_points_checked
  · exact Row058.promoted_points_checked
  · exact Row059.promoted_points_checked
  · exact Row060.promoted_points_checked
  · exact Row061.promoted_points_checked
  · exact Row062.promoted_points_checked
  · exact Row063.promoted_points_checked

/-- The actual pose rows and the actual old owned hull are explicit premises.
No root, pruning program, or whole case is asserted by this certificate. -/
theorem certificate_checked (s : PoseState)
    (hr : s.rows (4 : Owner) = retainedRows)
    (ho : s.owned (4 : Owner) = priorOwned) :
    ownershipCertificate.Check s (4 : Owner) := by
  refine ⟨?_, all_rows_points_checked, ?_⟩
  · change checkedRows.map Prod.fst = s.rows (4 : Owner)
    rw [hr]
    rfl
  · change HullVerticesCheck (s.owned (4 : Owner) ++ freshVertices) nextOwned nextWitnesses
    rw [ho]
    exact retained_hull_checked

theorem verified_promotion (s : PoseState)
    (hr : s.rows (4 : Owner) = retainedRows)
    (ho : s.owned (4 : Owner) = priorOwned) :
    VerifiedStep s (replaceHull s (4 : Owner) nextOwned) :=
  checked_ownership_step s (4 : Owner) ownershipCertificate (certificate_checked s hr ho)

theorem packing_promotion_holds {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s)
    (hr : s.rows (4 : Owner) = retainedRows)
    (ho : s.owned (4 : Owner) = priorOwned) :
    StateHolds P (replaceHull s (4 : Owner) nextOwned) :=
  verified_step_sound P hs (verified_promotion s hr ho)

end
end ElevenSquare.Tasks.T02.Prior1000Step000Ownership
