import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C00
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C01
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C02
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C03
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C04
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C05
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C06
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C07
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C08
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C09
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C10
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C11
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C12
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C13
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C14
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C15
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C16
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C17
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C18
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C19
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C20
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C21
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C22
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C23
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C24
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C25
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C26
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C27
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C28
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C29
import ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C30
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000

private def assignmentChunks : List (List (ℕ × Group)) := [
  CoverageChunks.C00.assignments, CoverageChunks.C01.assignments, CoverageChunks.C02.assignments, CoverageChunks.C03.assignments, CoverageChunks.C04.assignments, CoverageChunks.C05.assignments, CoverageChunks.C06.assignments, CoverageChunks.C07.assignments, CoverageChunks.C08.assignments, CoverageChunks.C09.assignments, CoverageChunks.C10.assignments, CoverageChunks.C11.assignments, CoverageChunks.C12.assignments, CoverageChunks.C13.assignments, CoverageChunks.C14.assignments, CoverageChunks.C15.assignments, CoverageChunks.C16.assignments, CoverageChunks.C17.assignments, CoverageChunks.C18.assignments, CoverageChunks.C19.assignments, CoverageChunks.C20.assignments, CoverageChunks.C21.assignments, CoverageChunks.C22.assignments, CoverageChunks.C23.assignments, CoverageChunks.C24.assignments, CoverageChunks.C25.assignments, CoverageChunks.C26.assignments, CoverageChunks.C27.assignments, CoverageChunks.C28.assignments, CoverageChunks.C29.assignments, CoverageChunks.C30.assignments]

private theorem array_toList_append (a b : Array ℕ) :
    (a ++ b).toList = a.toList ++ b.toList := by simp

private theorem baseline_array_assignments :
    baselineArray.toList = (assignmentChunks.join.map Prod.fst) := by
  simp [baselineArray, assignmentChunks, array_toList_append, List.append_assoc,
      ← CoverageChunks.C00.keys_match,
      ← CoverageChunks.C01.keys_match,
      ← CoverageChunks.C02.keys_match,
      ← CoverageChunks.C03.keys_match,
      ← CoverageChunks.C04.keys_match,
      ← CoverageChunks.C05.keys_match,
      ← CoverageChunks.C06.keys_match,
      ← CoverageChunks.C07.keys_match,
      ← CoverageChunks.C08.keys_match,
      ← CoverageChunks.C09.keys_match,
      ← CoverageChunks.C10.keys_match,
      ← CoverageChunks.C11.keys_match,
      ← CoverageChunks.C12.keys_match,
      ← CoverageChunks.C13.keys_match,
      ← CoverageChunks.C14.keys_match,
      ← CoverageChunks.C15.keys_match,
      ← CoverageChunks.C16.keys_match,
      ← CoverageChunks.C17.keys_match,
      ← CoverageChunks.C18.keys_match,
      ← CoverageChunks.C19.keys_match,
      ← CoverageChunks.C20.keys_match,
      ← CoverageChunks.C21.keys_match,
      ← CoverageChunks.C22.keys_match,
      ← CoverageChunks.C23.keys_match,
      ← CoverageChunks.C24.keys_match,
      ← CoverageChunks.C25.keys_match,
      ← CoverageChunks.C26.keys_match,
      ← CoverageChunks.C27.keys_match,
      ← CoverageChunks.C28.keys_match,
      ← CoverageChunks.C29.keys_match,
      ← CoverageChunks.C30.keys_match]

private theorem assignments_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) assignmentChunks.join := by
  have hchunks : List.Forall (List.Forall (fun p => p.1 ∈ groupCases p.2))
      assignmentChunks := by
    simp only [assignmentChunks, List.forall_cons]
    exact ⟨CoverageChunks.C00.valid, CoverageChunks.C01.valid, CoverageChunks.C02.valid, CoverageChunks.C03.valid, CoverageChunks.C04.valid, CoverageChunks.C05.valid, CoverageChunks.C06.valid, CoverageChunks.C07.valid, CoverageChunks.C08.valid, CoverageChunks.C09.valid, CoverageChunks.C10.valid, CoverageChunks.C11.valid, CoverageChunks.C12.valid, CoverageChunks.C13.valid, CoverageChunks.C14.valid, CoverageChunks.C15.valid, CoverageChunks.C16.valid, CoverageChunks.C17.valid, CoverageChunks.C18.valid, CoverageChunks.C19.valid, CoverageChunks.C20.valid, CoverageChunks.C21.valid, CoverageChunks.C22.valid, CoverageChunks.C23.valid, CoverageChunks.C24.valid, CoverageChunks.C25.valid, CoverageChunks.C26.valid, CoverageChunks.C27.valid, CoverageChunks.C28.valid, CoverageChunks.C29.valid, CoverageChunks.C30.valid, trivial⟩
  apply List.forall_iff_forall_mem.mpr
  intro p hp
  obtain ⟨row, hr, hpr⟩ := List.mem_join.mp hp
  exact (List.forall_iff_forall_mem.mp
    ((List.forall_iff_forall_mem.mp hchunks) row hr)) p hpr

/-- Every index in the public baseline family belongs to an explicit roster group. -/
theorem inventory_covered (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    ∃ g : Group, k.val ∈ groupCases g := by
  have h : k.val ∈ assignmentChunks.join.map Prod.fst := by
    rw [← baseline_array_assignments]
    exact List.mem_toFinset.mp hk
  obtain ⟨p, hp, hpk⟩ := List.mem_map.mp h
  refine ⟨p.2, ?_⟩
  have hp_valid := (List.forall_iff_forall_mem.mp assignments_valid) p hp
  simpa [hpk] using hp_valid

end
end ElevenSquare.Tasks.T01.Handoff
