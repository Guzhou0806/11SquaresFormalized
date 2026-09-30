import ElevenSquare.Pending.S08_SATNecessityCore
import ElevenSquare.Pending.GeometryTypes

namespace ElevenSquare.Pending
noncomputable section

/-- Necessity for arbitrary independently rotated squares. Boundary contact is legal. -/
theorem separating_axis_necessary (a b : UnitSquare)
    (hdisjoint : SquaresDisjoint a b) :
    ∃ v ∈ ([a.axis, -a.axis, perp a.axis, -(perp a.axis),
      b.axis, -b.axis, perp b.axis, -(perp b.axis)] : List Point),
      projectionRadius a v + projectionRadius b v ≤ dot (b.center-a.center) v := by
  exact SATNecessity.necessary a b hdisjoint

#print axioms separating_axis_necessary
end
end ElevenSquare.Pending
