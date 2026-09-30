import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window023.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window023
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-4339271553738761105568537/6221305527577000000000000), (72375162032354243069919/888757932511000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-4339271553738761105568537/6221305527577000000000000), (72375162032354243069919/888757932511000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-4339271553738761105568537/6221305527577000000000000), (72375162032354243069919/888757932511000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window023

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window023.core_checked
