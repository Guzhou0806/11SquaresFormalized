import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.InitialStateData
import ElevenSquare.Tasks.T03.Batch12.Seed2135

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.InitialState
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

noncomputable def state : PoseState := InitialStateData.state
theorem source_binding : state = ElevenSquare.Pending.T03.Batch12.Seed2135.state := by
  apply congrArg₂ PoseState.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
theorem initial (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2135)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  rw [source_binding]
  exact ElevenSquare.Pending.T03.Batch12.Seed2135.initializes P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.InitialState
