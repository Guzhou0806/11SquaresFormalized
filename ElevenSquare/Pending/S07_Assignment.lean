import ElevenSquare.Pending.S07_Data
namespace ElevenSquare.Pending
noncomputable section
-- An entirely FINITE predicate. No orientation or continuous geometry enters it.
def AvoidingAssignment (f : Owner → Fin 220) : Prop :=
  (∀ g : Fin 4, Function.Injective (fun i => overlayLabels (f i) g)) ∧
  (∀ g : Fin 4, Finset.univ.image (fun i => overlayLabels (f i) g) ∈ otherRawMasks) ∧
  (∀ i j : Owner, i ≠ j → ¬ pairBanned (f i) (f j))

end
end ElevenSquare.Pending
