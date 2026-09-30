import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window003.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-2313701590262182059283143273/4523466045742697000000000000), (2190516355016349390101402217/4523466045742697000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-2313701590262182059283143273/4523466045742697000000000000), (2190516355016349390101402217/4523466045742697000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-2313701590262182059283143273/4523466045742697000000000000), (2190516355016349390101402217/4523466045742697000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window003.core_checked
