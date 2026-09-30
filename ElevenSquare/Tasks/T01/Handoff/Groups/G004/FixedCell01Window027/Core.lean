import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-64264880070114446184433593/123741904501177000000000000), (-58855776602918308500530247/123741904501177000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-64264880070114446184433593/123741904501177000000000000), (-58855776602918308500530247/123741904501177000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-64264880070114446184433593/123741904501177000000000000), (-58855776602918308500530247/123741904501177000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027.core_checked
