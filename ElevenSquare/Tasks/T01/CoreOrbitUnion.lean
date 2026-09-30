import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- An eight-vertex common core needs checks at just two orbit representatives. -/
theorem baseline_core_vertices_of_two_orbits (Q : List QPoint)
    (v₀ v₁ : QPoint) (l u : ℚ)
    (hQ : ∀ w ∈ Q, w ∈ coreQuarterTurnOrbit v₀ ∨ w ∈ coreQuarterTurnOrbit v₁)
    (h₀ : BaselineCoreVertexCheck v₀ l u)
    (h₁ : BaselineCoreVertexCheck v₁ l u) :
    ∀ w ∈ Q, BaselineCoreVertexCheck w l u := by
  intro w hw
  rcases hQ w hw with h | h
  · exact baseline_core_quarter_turn_orbit_checked v₀ l u h₀ w h
  · exact baseline_core_quarter_turn_orbit_checked v₁ l u h₁ w h

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.baseline_core_vertices_of_two_orbits
