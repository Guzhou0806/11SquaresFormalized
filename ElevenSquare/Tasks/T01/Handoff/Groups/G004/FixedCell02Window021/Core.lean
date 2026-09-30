import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window021.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window021
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-15383945895468728559121/29872767121000000000000), (-13973954520471594693871/29872767121000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-15383945895468728559121/29872767121000000000000), (-13973954520471594693871/29872767121000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-15383945895468728559121/29872767121000000000000), (-13973954520471594693871/29872767121000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window021

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window021.core_checked
