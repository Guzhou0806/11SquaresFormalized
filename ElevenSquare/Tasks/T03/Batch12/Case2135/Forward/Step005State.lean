import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.RowData
import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step004State
import ElevenSquare.Tasks.T03.Batch12.Case2135.Node000.Step005Data
import ElevenSquare.Tasks.T03.RefinementRows

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step005State
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step005Data
noncomputable def before : PoseState := Step004State.state
noncomputable def entries : List (IntegerRow × RowRefinement) := [(RowData.InitialCell10Row000,.leaf),(RowData.InitialCell10Row001,.leaf),(RowData.InitialCell10Row002,.leaf),(RowData.InitialCell10Row003,.leaf),(RowData.InitialCell10Row004,.leaf),(RowData.InitialCell10Row005,.leaf),(RowData.InitialCell10Row006,.leaf),(RowData.InitialCell10Row007,.leaf)]
noncomputable def refined : PoseState := replaceRows before owner (RefinementRows.after entries)
noncomputable def afterRows : List PoseRow := []
noncomputable def state : PoseState := ⟨![[RowData.Node000Step003Row000.row,RowData.Node000Step003Row001.row,RowData.Node000Step003Row002.row,RowData.Node000Step003Row003.row,RowData.Node000Step003Row004.row,RowData.Node000Step003Row005.row,RowData.Node000Step003Row006.row,RowData.Node000Step003Row007.row],[RowData.InitialCell02Row000.row,RowData.InitialCell02Row001.row,RowData.InitialCell02Row002.row,RowData.InitialCell02Row003.row,RowData.InitialCell02Row004.row,RowData.InitialCell02Row005.row,RowData.InitialCell02Row006.row,RowData.InitialCell02Row007.row],[RowData.InitialCell03Row000.row,RowData.InitialCell03Row001.row,RowData.InitialCell03Row002.row,RowData.InitialCell03Row003.row,RowData.InitialCell03Row004.row,RowData.InitialCell03Row005.row,RowData.InitialCell03Row006.row,RowData.InitialCell03Row007.row],[RowData.Node000Step000Row000.row,RowData.Node000Step000Row001.row,RowData.Node000Step000Row002.row,RowData.Node000Step000Row003.row,RowData.Node000Step000Row004.row,RowData.Node000Step000Row005.row,RowData.Node000Step000Row006.row,RowData.Node000Step000Row007.row],[RowData.InitialCell07Row000.row,RowData.InitialCell07Row001.row,RowData.InitialCell07Row002.row,RowData.InitialCell07Row003.row,RowData.InitialCell07Row004.row,RowData.InitialCell07Row005.row,RowData.InitialCell07Row006.row,RowData.InitialCell07Row007.row],[RowData.Node000Step002Row000.row,RowData.Node000Step002Row001.row,RowData.Node000Step002Row002.row,RowData.Node000Step002Row003.row,RowData.Node000Step002Row004.row,RowData.Node000Step002Row005.row,RowData.Node000Step002Row006.row,RowData.Node000Step002Row007.row],[RowData.Node000Step001Row000.row,RowData.Node000Step001Row001.row,RowData.Node000Step001Row002.row,RowData.Node000Step001Row003.row,RowData.Node000Step001Row004.row,RowData.Node000Step001Row005.row,RowData.Node000Step001Row006.row,RowData.Node000Step001Row007.row],[],[RowData.InitialCell11Row000.row,RowData.InitialCell11Row001.row,RowData.InitialCell11Row002.row,RowData.InitialCell11Row003.row,RowData.InitialCell11Row004.row,RowData.InitialCell11Row005.row,RowData.InitialCell11Row006.row,RowData.InitialCell11Row007.row],[RowData.Node000Step004Row000.row,RowData.Node000Step004Row001.row,RowData.Node000Step004Row002.row,RowData.Node000Step004Row003.row,RowData.Node000Step004Row004.row,RowData.Node000Step004Row005.row,RowData.Node000Step004Row006.row,RowData.Node000Step004Row007.row],[RowData.InitialCell14Row000.row,RowData.InitialCell14Row001.row,RowData.InitialCell14Row002.row,RowData.InitialCell14Row003.row,RowData.InitialCell14Row004.row,RowData.InitialCell14Row005.row,RowData.InitialCell14Row006.row,RowData.InitialCell14Row007.row]],Function.update prior owner chosen⟩
theorem partition_checked : RefinementRows.check entries = true := by rfl
theorem before_binding : before.rows owner = RefinementRows.before entries := by rfl
theorem prior_binding : refined.owned = prior := by funext i; fin_cases i <;> rfl
theorem state_binding : replaceHull (replaceRows refined owner afterRows) owner chosen = state := by
  apply congrArg₂ PoseState.mk
  · funext i; fin_cases i <;> rfl
  · change Function.update refined.owned owner chosen = Function.update prior owner chosen
    rw [prior_binding]

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step005State
