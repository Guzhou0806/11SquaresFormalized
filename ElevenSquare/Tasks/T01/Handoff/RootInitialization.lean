import ElevenSquare.Tasks.T01.Handoff.RootData
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- Closed cell occupancy and charted orientations initialize the rational seed
state, including a relabeling permutation and strict owned hulls. -/
theorem root_initialized
    (g : Group) (k : Fin 2184) (hk : k.val ∈ groupCases g) :
    RootValid (caseMask k) (rootData g k) := by
  intro P hc ho
  exact ElevenSquare.Tasks.T01.uniform_seed_root_initialized P
    (rootBinCount g) (rootBinCount_pos g) (caseMask k) hc ho

end
end ElevenSquare.Tasks.T01.Handoff
