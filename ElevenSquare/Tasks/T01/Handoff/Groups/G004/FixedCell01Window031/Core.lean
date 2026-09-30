import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window031.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window031
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-68466028420750026764109649/135880991152465000000000000), (-66870648711778230133957807/135880991152465000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-68466028420750026764109649/135880991152465000000000000), (-66870648711778230133957807/135880991152465000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-68466028420750026764109649/135880991152465000000000000), (-66870648711778230133957807/135880991152465000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window031

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window031.core_checked
