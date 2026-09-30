import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedCell01
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedCell02
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedCell04
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedCell05
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedCell08
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedCell11
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedCell14

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_roster_full_chart : OwnedRosterFullChart := by
  intro c q hcell hcont hchart v hv
  fin_cases c
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ownedRosterCell01 at hv
    exact owned_cell01 q hcell hcont hchart v hv
  · change v ∈ ownedRosterCell02 at hv
    exact owned_cell02 q hcell hcont hchart v hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ownedRosterCell04 at hv
    exact owned_cell04 q hcell hcont hchart v hv
  · change v ∈ ownedRosterCell05 at hv
    exact owned_cell05 q hcell hcont hchart v hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ownedRosterCell08 at hv
    exact owned_cell08 q hcell hcont hchart v hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ownedRosterCell11 at hv
    exact owned_cell11 q hcell hcont hchart v hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv
  · change v ∈ ownedRosterCell14 at hv
    exact owned_cell14 q hcell hcont hchart v hv
  · change v ∈ ([] : List QPoint) at hv
    simp at hv

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.owned_roster_full_chart
