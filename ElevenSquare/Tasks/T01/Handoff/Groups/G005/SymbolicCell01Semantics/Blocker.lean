import ElevenSquare.Tasks.T01.Handoff.Groups.G005.Support
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def blockPoint : QPoint := (498020679/500000000, 872404559/1000000000)

theorem block_point_owned (P : Packing 11 coverCap)
    (hc : IsCharted P) (owners : Fin 16 → Owner)
    (hs : G005.SupportOwners P owners) :
    ∃ j : Owner, owners 1 ≠ j ∧
      OpenSquare (P.squares j) (realPoint blockPoint) := by
  refine ⟨owners 0, ?_, ?_⟩
  · exact hs.2 1 (by decide) 0 (by decide) (by decide)
  · have hcell : ClosedCell 0
        (normalizeCenter (P.squares (owners 0)).center) :=
      hs.1 0 (by decide)
    simpa [blockPoint,
      ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.ownedP005] using
      (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.gate_point005_owned
        (P.squares (owners 0)) hcell (P.contained (owners 0))
        (hc (owners 0)))

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.block_point_owned
