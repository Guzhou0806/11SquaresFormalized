import ElevenSquare.Tasks.T01.Handoff.PlanData
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- CALCULATION / FINITE-STRUCTURE HOLE. Empty-row/collision witnesses,
or majority cardinality and distinct owners. Every leaf must close. -/
theorem leaf_calculations (g : Group) (hselected : ReducedCoverage.Selected g)
    (k : Fin 2184) (hk : k.val ∈ groupCases g) :
    (planData g k).LeafChecks (rootData g k) := by
  sorry

end
end ElevenSquare.Tasks.T01.Handoff
