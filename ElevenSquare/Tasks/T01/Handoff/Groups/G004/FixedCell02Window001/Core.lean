import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window001.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-2278223758468089289096413777/4521536426292817000000000000), (130908504885976662292248129/265972730958401000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-2278223758468089289096413777/4521536426292817000000000000), (130908504885976662292248129/265972730958401000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-2278223758468089289096413777/4521536426292817000000000000), (130908504885976662292248129/265972730958401000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window001

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window001.core_checked
