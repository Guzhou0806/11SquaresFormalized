import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 1. -/
def sharedRosterCell01 : List QPoint := [((78686667498184714830022331/50000000000000000000000000), (63091593459680811351013693/100000000000000000000000000)), ((78936667498184714830022331/50000000000000000000000000), (63091593459680811351013693/100000000000000000000000000)), ((78436667498184714830022331/50000000000000000000000000), (63091593459680811351013693/100000000000000000000000000)), ((78686667498184714830022331/50000000000000000000000000), (63591593459680811351013693/100000000000000000000000000)), ((78686667498184714830022331/50000000000000000000000000), (62591593459680811351013693/100000000000000000000000000)), ((1603637329/1000000000), (63990253/100000000)), ((1572048057/1000000000), (232270007/250000000)), ((1543883109/1000000000), (339364257/500000000)), ((1543883109/1000000000), (629214151/1000000000)), ((783959637/500000000), (305477393/500000000))]

theorem sharedRosterCell01_owned (q : UnitSquare)
    (hcell : ClosedCell 1 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell01, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell01, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.gate_point007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.ownedP008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.gate_point008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point009_owned q hcell)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell01_owned
