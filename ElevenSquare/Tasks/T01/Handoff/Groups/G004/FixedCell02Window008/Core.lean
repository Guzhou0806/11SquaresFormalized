import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window008.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-611400734026258290765801/1125669324521000000000000), (490516956746503796690409/1125669324521000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-611400734026258290765801/1125669324521000000000000), (490516956746503796690409/1125669324521000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-611400734026258290765801/1125669324521000000000000), (490516956746503796690409/1125669324521000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window008

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window008.core_checked
