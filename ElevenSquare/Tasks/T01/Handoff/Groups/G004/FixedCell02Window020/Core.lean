import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window020.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window020
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-214854527499555577521/406497265000000000000), (-176288192499635351247/406497265000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-214854527499555577521/406497265000000000000), (-176288192499635351247/406497265000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-214854527499555577521/406497265000000000000), (-176288192499635351247/406497265000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window020

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window020.core_checked
