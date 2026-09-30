import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window079.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window079
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-14586458714158202454736041/26892122605225000000000000), (-12073050853788250745208663/26892122605225000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-14586458714158202454736041/26892122605225000000000000), (-12073050853788250745208663/26892122605225000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-14586458714158202454736041/26892122605225000000000000), (-12073050853788250745208663/26892122605225000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window079

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window079.core_checked
