import ElevenSquare.Tasks.T01.Handoff.PlanData
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- CALCULATION / FINITE-STRUCTURE HOLE. Exact rational core, wall, Farkas,
cover and ownership checks; also exact row identities and predecessor links. -/
theorem program_calculations (g : Group) (hselected : ReducedCoverage.Selected g)
    (k : Fin 2184) (hk : k.val ∈ groupCases g) :
    (planData g k).ProgramChecks (rootData g k) := by
  sorry

end
end ElevenSquare.Tasks.T01.Handoff
