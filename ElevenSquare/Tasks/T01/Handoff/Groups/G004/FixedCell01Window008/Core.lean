import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-73459571499845334153/109375433000000000000), (1001523499997891337/109375433000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-73459571499845334153/109375433000000000000), (1001523499997891337/109375433000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-73459571499845334153/109375433000000000000), (1001523499997891337/109375433000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008.core_checked
