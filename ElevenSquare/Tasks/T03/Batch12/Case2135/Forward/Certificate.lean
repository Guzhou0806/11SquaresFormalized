import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step005Trace

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step005Trace.state := Or.inl ⟨7,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 2135) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 2135) InitialState.state Step005Trace.state
    InitialState.initial Step005Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Certificate
