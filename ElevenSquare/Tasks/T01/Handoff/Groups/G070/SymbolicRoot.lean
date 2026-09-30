import ElevenSquare.Tasks.T01.Handoff.Groups.G070.RootData
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.SymbolicSlabRoot

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots
noncomputable section

/-- The G070 initial state uses the rational slab derived from the two angle
    endpoints. The archived wall polygons are unnecessary for initialization. -/
def root : PoseState where
  rows := fun i => slabRows 32 (G070.physicalCell i)
  owned := G070.ownedAt

theorem initialized_of_pointwise_ownership
    (hpoints : ∀ (i : Owner) (q : UnitSquare),
      ClosedCell (G070.physicalCell i) (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      ∀ p ∈ G070.ownedAt i, OpenSquare q (realPoint p)) :
    RootValid G070.mask root := by
  intro P hc ho
  have ho' : Occupies P (Finset.univ.image G070.physicalCell) := by
    rwa [G070.physicalCell_image]
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P G070.physicalCell
    G070.physicalCell_injective ho'
  refine ⟨perm, ?_, ?_⟩
  · intro i
    exact slab_rows_contain 32 (by decide) _ _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))
  · intro i
    exact hull_owned_of_vertices _ _
      (hpoints i _ (hcell i)
        ((relabelPacking P perm).contained i) (hc (perm i)))

/-- G070's terminal owner is physical cell 14, hence owner index 10. Its
    first pose domain is never pruned before the terminal step, so it can
    start with eight wider angle bins while the other owners keep 32. -/
def terminalCoarseRowCount (i : Owner) : ℕ :=
  if i = (10 : Owner) then 8 else 32

theorem terminalCoarseRowCount_pos (i : Owner) :
    0 < terminalCoarseRowCount i := by
  by_cases hi : i = (10 : Owner)
  · simp [terminalCoarseRowCount, hi]
  · simp [terminalCoarseRowCount, hi]

def terminalCoarseRoot : PoseState where
  rows := fun i => slabRows (terminalCoarseRowCount i) (G070.physicalCell i)
  owned := G070.ownedAt

theorem terminal_coarse_initialized_of_pointwise_ownership
    (hpoints : ∀ (i : Owner) (q : UnitSquare),
      ClosedCell (G070.physicalCell i) (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      ∀ p ∈ G070.ownedAt i, OpenSquare q (realPoint p)) :
    RootValid G070.mask terminalCoarseRoot := by
  intro P hc ho
  have ho' : Occupies P (Finset.univ.image G070.physicalCell) := by
    rwa [G070.physicalCell_image]
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P G070.physicalCell
    G070.physicalCell_injective ho'
  refine ⟨perm, ?_, ?_⟩
  · intro i
    exact slab_rows_contain (terminalCoarseRowCount i)
      (terminalCoarseRowCount_pos i) _ _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))
  · intro i
    exact hull_owned_of_vertices _ _
      (hpoints i _ (hcell i)
        ((relabelPacking P perm).contained i) (hc (perm i)))

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot.initialized_of_pointwise_ownership
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRoot.terminal_coarse_initialized_of_pointwise_ownership
