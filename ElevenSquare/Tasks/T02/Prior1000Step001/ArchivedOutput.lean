import ElevenSquare.Tasks.T02.Prior1000Step001.Complete
import ElevenSquare.Tasks.T02.PoseStateRelaxation

namespace ElevenSquare.Tasks.T02.Prior1000Step001
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

/-- Exact retained/archived row pairs, preserving each row's interval. -/
def archivePairs : List (PoseRow × PoseRow) := [
  (Prior1000Step001Row000.retainedRow, {Prior1000Step001Row000.retainedRow with centers := Prior1000Step001Row000.archivedOuterPolygon}),
  (Prior1000Step001Row001.retainedRow, {Prior1000Step001Row001.retainedRow with centers := Prior1000Step001Row001.archivedOuterPolygon}),
  (Prior1000Step001Row002.retainedRow, {Prior1000Step001Row002.retainedRow with centers := Prior1000Step001Row002.archivedOuterPolygon}),
  (Prior1000Step001Row003.retainedRow, {Prior1000Step001Row003.retainedRow with centers := Prior1000Step001Row003.archivedOuterPolygon}),
  (Prior1000Step001Row004.retainedRow, {Prior1000Step001Row004.retainedRow with centers := Prior1000Step001Row004.archivedOuterPolygon}),
  (Prior1000Step001Row005.retainedRow, {Prior1000Step001Row005.retainedRow with centers := Prior1000Step001Row005.archivedOuterPolygon}),
  (Prior1000Step001Row006.retainedRow, {Prior1000Step001Row006.retainedRow with centers := Prior1000Step001Row006.archivedOuterPolygon}),
  (Prior1000Step001Row007.retainedRow, {Prior1000Step001Row007.retainedRow with centers := Prior1000Step001Row007.archivedOuterPolygon}),
  (Prior1000Step001Row008.retainedRow, {Prior1000Step001Row008.retainedRow with centers := Prior1000Step001Row008.archivedOuterPolygon}),
  (Prior1000Step001Row009.retainedRow, {Prior1000Step001Row009.retainedRow with centers := Prior1000Step001Row009.archivedOuterPolygon}),
  (Prior1000Step001Row010.retainedRow, {Prior1000Step001Row010.retainedRow with centers := Prior1000Step001Row010.archivedOuterPolygon}),
  (Prior1000Step001Row011.retainedRow, {Prior1000Step001Row011.retainedRow with centers := Prior1000Step001Row011.archivedOuterPolygon}),
  (Prior1000Step001Row012.retainedRow, {Prior1000Step001Row012.retainedRow with centers := Prior1000Step001Row012.archivedOuterPolygon}),
  (Prior1000Step001Row013.retainedRow, {Prior1000Step001Row013.retainedRow with centers := Prior1000Step001Row013.archivedOuterPolygon}),
  (Prior1000Step001Row014.retainedRow, {Prior1000Step001Row014.retainedRow with centers := Prior1000Step001Row014.archivedOuterPolygon}),
  (Prior1000Step001Row015.retainedRow, {Prior1000Step001Row015.retainedRow with centers := Prior1000Step001Row015.archivedOuterPolygon}),
  (Prior1000Step001Row016.retainedRow, {Prior1000Step001Row016.retainedRow with centers := Prior1000Step001Row016.archivedOuterPolygon}),
  (Prior1000Step001Row017.retainedRow, {Prior1000Step001Row017.retainedRow with centers := Prior1000Step001Row017.archivedOuterPolygon}),
  (Prior1000Step001Row018.retainedRow, {Prior1000Step001Row018.retainedRow with centers := Prior1000Step001Row018.archivedOuterPolygon}),
  (Prior1000Step001Row019.retainedRow, {Prior1000Step001Row019.retainedRow with centers := Prior1000Step001Row019.archivedOuterPolygon}),
  (Prior1000Step001Row020.retainedRow, {Prior1000Step001Row020.retainedRow with centers := Prior1000Step001Row020.archivedOuterPolygon}),
  (Prior1000Step001Row021.retainedRow, {Prior1000Step001Row021.retainedRow with centers := Prior1000Step001Row021.archivedOuterPolygon}),
  (Prior1000Step001Row022.retainedRow, {Prior1000Step001Row022.retainedRow with centers := Prior1000Step001Row022.archivedOuterPolygon}),
  (Prior1000Step001Row023.retainedRow, {Prior1000Step001Row023.retainedRow with centers := Prior1000Step001Row023.archivedOuterPolygon}),
  (Prior1000Step001Row024.retainedRow, {Prior1000Step001Row024.retainedRow with centers := Prior1000Step001Row024.archivedOuterPolygon}),
  (Prior1000Step001Row025.retainedRow, {Prior1000Step001Row025.retainedRow with centers := Prior1000Step001Row025.archivedOuterPolygon}),
  (Prior1000Step001Row026.retainedRow, {Prior1000Step001Row026.retainedRow with centers := Prior1000Step001Row026.archivedOuterPolygon}),
  (Prior1000Step001Row027.retainedRow, {Prior1000Step001Row027.retainedRow with centers := Prior1000Step001Row027.archivedOuterPolygon}),
  (Prior1000Step001Row028.retainedRow, {Prior1000Step001Row028.retainedRow with centers := Prior1000Step001Row028.archivedOuterPolygon}),
  (Prior1000Step001Row029.retainedRow, {Prior1000Step001Row029.retainedRow with centers := Prior1000Step001Row029.archivedOuterPolygon}),
  (Prior1000Step001Row030.retainedRow, {Prior1000Step001Row030.retainedRow with centers := Prior1000Step001Row030.archivedOuterPolygon}),
  (Prior1000Step001Row031.retainedRow, {Prior1000Step001Row031.retainedRow with centers := Prior1000Step001Row031.archivedOuterPolygon}),
  (Prior1000Step001Row032.retainedRow, {Prior1000Step001Row032.retainedRow with centers := Prior1000Step001Row032.archivedOuterPolygon}),
  (Prior1000Step001Row033.retainedRow, {Prior1000Step001Row033.retainedRow with centers := Prior1000Step001Row033.archivedOuterPolygon}),
  (Prior1000Step001Row034.retainedRow, {Prior1000Step001Row034.retainedRow with centers := Prior1000Step001Row034.archivedOuterPolygon}),
  (Prior1000Step001Row035.retainedRow, {Prior1000Step001Row035.retainedRow with centers := Prior1000Step001Row035.archivedOuterPolygon}),
  (Prior1000Step001Row036.retainedRow, {Prior1000Step001Row036.retainedRow with centers := Prior1000Step001Row036.archivedOuterPolygon}),
  (Prior1000Step001Row037.retainedRow, {Prior1000Step001Row037.retainedRow with centers := Prior1000Step001Row037.archivedOuterPolygon}),
  (Prior1000Step001Row038.retainedRow, {Prior1000Step001Row038.retainedRow with centers := Prior1000Step001Row038.archivedOuterPolygon}),
  (Prior1000Step001Row039.retainedRow, {Prior1000Step001Row039.retainedRow with centers := Prior1000Step001Row039.archivedOuterPolygon}),
  (Prior1000Step001Row040.retainedRow, {Prior1000Step001Row040.retainedRow with centers := Prior1000Step001Row040.archivedOuterPolygon}),
  (Prior1000Step001Row041.retainedRow, {Prior1000Step001Row041.retainedRow with centers := Prior1000Step001Row041.archivedOuterPolygon}),
  (Prior1000Step001Row042.retainedRow, {Prior1000Step001Row042.retainedRow with centers := Prior1000Step001Row042.archivedOuterPolygon}),
  (Prior1000Step001Row043.retainedRow, {Prior1000Step001Row043.retainedRow with centers := Prior1000Step001Row043.archivedOuterPolygon}),
  (Prior1000Step001Row044.retainedRow, {Prior1000Step001Row044.retainedRow with centers := Prior1000Step001Row044.archivedOuterPolygon}),
  (Prior1000Step001Row045.retainedRow, {Prior1000Step001Row045.retainedRow with centers := Prior1000Step001Row045.archivedOuterPolygon}),
  (Prior1000Step001Row046.retainedRow, {Prior1000Step001Row046.retainedRow with centers := Prior1000Step001Row046.archivedOuterPolygon}),
  (Prior1000Step001Row047.retainedRow, {Prior1000Step001Row047.retainedRow with centers := Prior1000Step001Row047.archivedOuterPolygon}),
  (Prior1000Step001Row048.retainedRow, {Prior1000Step001Row048.retainedRow with centers := Prior1000Step001Row048.archivedOuterPolygon}),
  (Prior1000Step001Row049.retainedRow, {Prior1000Step001Row049.retainedRow with centers := Prior1000Step001Row049.archivedOuterPolygon}),
  (Prior1000Step001Row050.retainedRow, {Prior1000Step001Row050.retainedRow with centers := Prior1000Step001Row050.archivedOuterPolygon}),
  (Prior1000Step001Row051.retainedRow, {Prior1000Step001Row051.retainedRow with centers := Prior1000Step001Row051.archivedOuterPolygon}),
  (Prior1000Step001Row052.retainedRow, {Prior1000Step001Row052.retainedRow with centers := Prior1000Step001Row052.archivedOuterPolygon}),
  (Prior1000Step001Row053.retainedRow, {Prior1000Step001Row053.retainedRow with centers := Prior1000Step001Row053.archivedOuterPolygon}),
  (Prior1000Step001Row054.retainedRow, {Prior1000Step001Row054.retainedRow with centers := Prior1000Step001Row054.archivedOuterPolygon}),
  (Prior1000Step001Row055.retainedRow, {Prior1000Step001Row055.retainedRow with centers := Prior1000Step001Row055.archivedOuterPolygon}),
  (Prior1000Step001Row056.retainedRow, {Prior1000Step001Row056.retainedRow with centers := Prior1000Step001Row056.archivedOuterPolygon}),
  (Prior1000Step001Row057.retainedRow, {Prior1000Step001Row057.retainedRow with centers := Prior1000Step001Row057.archivedOuterPolygon}),
  (Prior1000Step001Row058.retainedRow, {Prior1000Step001Row058.retainedRow with centers := Prior1000Step001Row058.archivedOuterPolygon}),
  (Prior1000Step001Row059.retainedRow, {Prior1000Step001Row059.retainedRow with centers := Prior1000Step001Row059.archivedOuterPolygon}),
  (Prior1000Step001Row060.retainedRow, {Prior1000Step001Row060.retainedRow with centers := Prior1000Step001Row060.archivedOuterPolygon}),
  (Prior1000Step001Row061.retainedRow, {Prior1000Step001Row061.retainedRow with centers := Prior1000Step001Row061.archivedOuterPolygon}),
  (Prior1000Step001Row062.retainedRow, {Prior1000Step001Row062.retainedRow with centers := Prior1000Step001Row062.archivedOuterPolygon}),
  (Prior1000Step001Row063.retainedRow, {Prior1000Step001Row063.retainedRow with centers := Prior1000Step001Row063.archivedOuterPolygon})]

def archivedRows : List PoseRow := archivePairs.map Prod.snd

theorem archive_pairs_input : archivePairs.map Prod.fst = retainedRows := rfl

theorem archive_pairs_checked : ∀ pair ∈ archivePairs, ∀ q : UnitSquare,
    pair.1.contains q → pair.2.contains q := by
  intro pair hp
  simp only [archivePairs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pose_row_weaken _ _ Prior1000Step001Row000.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row001.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row002.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row003.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row004.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row005.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row006.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row007.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row008.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row009.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row010.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row011.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row012.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row013.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row014.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row015.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row016.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row017.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row018.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row019.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row020.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row021.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row022.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row023.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row024.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row025.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row026.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row027.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row028.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row029.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row030.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row031.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row032.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row033.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row034.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row035.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row036.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row037.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row038.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row039.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row040.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row041.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row042.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row043.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row044.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row045.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row046.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row047.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row048.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row049.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row050.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row051.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row052.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row053.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row054.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row055.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row056.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row057.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row058.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row059.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row060.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row061.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row062.retained_in_archived_outer
  · exact pose_row_weaken _ _ Prior1000Step001Row063.retained_in_archived_outer

theorem retained_rows_in_archive (q : UnitSquare) (hq : RowsContain retainedRows q) :
    RowsContain archivedRows q := by
  apply paired_rows_weaken archivePairs archive_pairs_checked q
  simpa only [archive_pairs_input] using hq

def archivedNextState (s : PoseState) : PoseState :=
  replaceRows (nextState s) (6 : Owner) archivedRows

theorem archived_rows_holds {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P (nextState s)) : StateHolds P (archivedNextState s) := by
  apply state_rows_weaken P (nextState s) (6 : Owner) archivedRows _ hs
  intro q hq
  apply retained_rows_in_archive q
  simpa only [nextState, replaceHull, replaceRows, Function.update_self] using hq

theorem archived_step_holds {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (hr : s.rows (6 : Owner) = predecessorRows)
    (ho : s.owned = ownedByRole) : StateHolds P (archivedNextState s) :=
  archived_rows_holds P s (step_holds P s hs hr ho)

end
end ElevenSquare.Tasks.T02.Prior1000Step001
