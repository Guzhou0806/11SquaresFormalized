import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 2. -/
def sharedRosterCell02 : List QPoint := [((464596403987128110649685633/200000000000000000000000000), (22480315265430140099670659/25000000000000000000000000)), ((465596403987128110649685633/200000000000000000000000000), (22480315265430140099670659/25000000000000000000000000)), ((463596403987128110649685633/200000000000000000000000000), (22480315265430140099670659/25000000000000000000000000)), ((464596403987128110649685633/200000000000000000000000000), (22605315265430140099670659/25000000000000000000000000)), ((464596403987128110649685633/200000000000000000000000000), (22355315265430140099670659/25000000000000000000000000)), ((294604953/125000000), (249496063/250000000)), ((1119317069/500000000), (249496063/250000000)), ((559224399/250000000), (1943513/1953125)), ((561353533/250000000), (6081077/6250000)), ((2265303257/1000000000), (930682669/1000000000)), ((580724397/250000000), (442208669/500000000)), ((292877443/125000000), (224655049/250000000))]

theorem sharedRosterCell02_owned (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell02, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell02, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point009_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point010_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP6] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point011_owned q hcell)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell02_owned
