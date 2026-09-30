import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 7. -/
def sharedRosterCell07 : List QPoint := [((153156523725617232432678909/50000000000000000000000000), (73266817431299737482805753/50000000000000000000000000)), ((153406523725617232432678909/50000000000000000000000000), (73266817431299737482805753/50000000000000000000000000)), ((152906523725617232432678909/50000000000000000000000000), (73266817431299737482805753/50000000000000000000000000)), ((153156523725617232432678909/50000000000000000000000000), (73516817431299737482805753/50000000000000000000000000)), ((153156523725617232432678909/50000000000000000000000000), (73016817431299737482805753/50000000000000000000000000)), ((3080549913/1000000000), (1452336041/1000000000)), ((1533873877/500000000), (1486952043/1000000000)), ((3047858629/1000000000), (305848339/200000000)), ((3018841763/1000000000), (1554336589/1000000000)), ((728792327/250000000), (1520103527/1000000000)), ((180050283/62500000), (1504634021/1000000000)), ((180050283/62500000), (1448584901/1000000000)), ((2944795153/1000000000), (1418113041/1000000000)), ((2993103927/1000000000), (1399934221/1000000000)), ((1486197139/500000000), (1541873753/1000000000))]

theorem sharedRosterCell07_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell07, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell07, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.gate_point005_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point009_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point010_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point011_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP012] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point012_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP013] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point013_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.ownedP014] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.gate_point014_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell07_owned
