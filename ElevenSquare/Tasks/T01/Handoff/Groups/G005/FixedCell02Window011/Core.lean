import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window011.Data
import ElevenSquare.Tasks.T01.CoreVertexSymmetry

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window011
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four strict quadratic checks at one corner suffice by square symmetry. -/
theorem first_vertex_checked :
    BaselineCoreVertexCheck ((-3810405931240698999679410249/5589341395981385000000000000), (58477951857710119164046521/328784787998905000000000000)) inputRow.lo inputRow.hi := by
  norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

theorem core_is_quarter_turn_orbit : core = coreQuarterTurnOrbit ((-3810405931240698999679410249/5589341395981385000000000000), (58477951857710119164046521/328784787998905000000000000)) := by
  norm_num [core, coreQuarterTurnOrbit]

theorem core_checked : ∀ w ∈ core, BaselineCoreVertexCheck w inputRow.lo inputRow.hi := by
  rw [core_is_quarter_turn_orbit]
  exact baseline_core_quarter_turn_orbit_checked ((-3810405931240698999679410249/5589341395981385000000000000), (58477951857710119164046521/328784787998905000000000000)) inputRow.lo inputRow.hi
    first_vertex_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window011

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window011.core_checked
