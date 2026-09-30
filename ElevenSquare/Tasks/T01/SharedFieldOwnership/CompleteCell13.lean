import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 13. -/
def sharedRosterCell13 : List QPoint := [((310820314017434724812314367/200000000000000000000000000), (74446774485140214333079341/25000000000000000000000000)), ((311820314017434724812314367/200000000000000000000000000), (74446774485140214333079341/25000000000000000000000000)), ((309820314017434724812314367/200000000000000000000000000), (74446774485140214333079341/25000000000000000000000000)), ((310820314017434724812314367/200000000000000000000000000), (74571774485140214333079341/25000000000000000000000000)), ((310820314017434724812314367/200000000000000000000000000), (74321774485140214333079341/25000000000000000000000000)), ((820092997/500000000), (1441002467/500000000)), ((815834729/500000000), (290411127/100000000)), ((1611780333/1000000000), (2946400921/1000000000)), ((777093001/500000000), (748166563/250000000)), ((767032023/500000000), (595692679/200000000)), ((760121983/500000000), (1439549669/500000000)), ((409612363/250000000), (1439549669/500000000))]

theorem sharedRosterCell13_owned (q : UnitSquare)
    (hcell : ClosedCell 13 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell13, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell13, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.originalP13_005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.mirror_cell13_gate005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.originalP13_006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.mirror_cell13_gate006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.originalP13_007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.mirror_cell13_gate007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.gate_point008_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.ownedP6] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell13.gate_point009_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.originalP13_010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.mirror_cell13_gate010_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.originalP13_011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.mirror_cell13_gate011_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell13_owned
