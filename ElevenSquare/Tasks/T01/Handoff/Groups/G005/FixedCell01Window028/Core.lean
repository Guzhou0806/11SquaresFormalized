import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window028.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window028
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-66165607632554235537464481/95426067045025000000000000), (10565642000666219690592417/95426067045025000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-66165607632554235537464481/95426067045025000000000000), (10565642000666219690592417/95426067045025000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-66165607632554235537464481/95426067045025000000000000), (10565642000666219690592417/95426067045025000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window028

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window028.core_checked
