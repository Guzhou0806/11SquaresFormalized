import ElevenSquare.Tasks.T01.Handoff.Groups.G007.ChoicePlan
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row000.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Partner

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.Row000ChoiceSample
open ElevenSquare.Pending ElevenSquare.Tasks.T01 ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

/-- Exact checked choice for the closed interval ['0', '1/32']. -/
def row000Certificate (partner : Fin 16 → Owner) : ChoiceRowCertificate where
  row := Cell05Row000.inputRow
  blocks := [
    rosterBlock partner ⟨1, by decide⟩ 2,
    rosterBlock partner ⟨1, by decide⟩ 3,
    rosterBlock partner ⟨4, by decide⟩ 0,
    rosterBlock partner ⟨4, by decide⟩ 7
  ]
  choice := by
    intro q hq hb
    exact Cell05Row000.row_choice q hq (by simpa [Cell05Row000.forbiddenPoints] using hb)

def sampleState (m : Finset (Fin 16)) : PoseState where
  rows := fun _ => []
  owned := fun i => ownedRoster (baselineRoles m i)

theorem sample_check (m : Finset (Fin 16)) (hm : m.card = 11)
    (h1 : (⟨1, by decide⟩ : Fin 16) ∈ m)
    (h4 : (⟨4, by decide⟩ : Fin 16) ∈ m)
    (h5 : (⟨5, by decide⟩ : Fin 16) ∈ m) :
    (row000Certificate (partner m)).Check (sampleState m) (partner m 5) := by
  simp only [ChoiceRowCertificate.Check, row000Certificate,
    List.forall_cons]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · exact roster_block_check (sampleState m) (partner m) 5 1 2
      (partner_ne hm h5 h1 (by decide))
      (by exact congrArg ownedRoster (partner_spec hm h1)) (by decide)
  · exact roster_block_check (sampleState m) (partner m) 5 1 3
      (partner_ne hm h5 h1 (by decide))
      (by exact congrArg ownedRoster (partner_spec hm h1)) (by decide)
  · exact roster_block_check (sampleState m) (partner m) 5 4 0
      (partner_ne hm h5 h4 (by decide))
      (by exact congrArg ownedRoster (partner_spec hm h4)) (by decide)
  · exact roster_block_check (sampleState m) (partner m) 5 4 7
      (partner_ne hm h5 h4 (by decide))
      (by exact congrArg ownedRoster (partner_spec hm h4)) (by decide)


end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.Row000ChoiceSample

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.Row000ChoiceSample.sample_check
