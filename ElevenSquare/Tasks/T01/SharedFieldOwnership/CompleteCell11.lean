import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 11. -/
def sharedRosterCell11 : List QPoint := [((616096720837113450472804689/200000000000000000000000000), (222515973933306985981279951/100000000000000000000000000)), ((617096720837113450472804689/200000000000000000000000000), (222515973933306985981279951/100000000000000000000000000)), ((615096720837113450472804689/200000000000000000000000000), (222515973933306985981279951/100000000000000000000000000)), ((616096720837113450472804689/200000000000000000000000000), (223015973933306985981279951/100000000000000000000000000)), ((616096720837113450472804689/200000000000000000000000000), (222015973933306985981279951/100000000000000000000000000)), ((3094392239/1000000000), (277553367/125000000)), ((3086707999/1000000000), (2246760407/1000000000)), ((3019092373/1000000000), (2290732051/1000000000)), ((733755081/250000000), (565346659/250000000)), ((288115159/100000000), (447239513/200000000)), ((288115159/100000000), (554210361/250000000)), ((734588649/250000000), (2189911489/1000000000)), ((752258247/250000000), (2164513839/1000000000)), ((1440671663/500000000), (2221138619/1000000000))]

theorem sharedRosterCell11_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell11, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell11, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell11.gate_point005_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate009_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate010_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate011_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_012] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate012_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_013] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate013_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell11_owned
