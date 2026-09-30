import ElevenSquare.Tasks.T01.Handoff.Plan
import ElevenSquare.Tasks.T01.WallSeedRoot

namespace ElevenSquare.Tasks.T01.Handoff.GenericBridge
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- Data for a generic root on a uniform closed chart partition.  The pose
    certificates specify the wall-clipped rows, while the ownership
    certificates justify each complete initial owned hull. -/
structure WallRootCertificate (n : ℕ) where
  pose : Fin 16 → CellRootCertificate n
  ownership : Fin 16 → WallOwnershipCertificate

def WallRootCertificate.root {n : ℕ} (c : WallRootCertificate n)
    (m : Finset (Fin 16)) : PoseState :=
  checkedSeedRoot c.pose m

/-- All occupied cells are checked.  In particular, `DomainCheck` checks every
    one of the `n` closed rows, and the ownership tree checks both sides of
    every angle split, including their shared boundary. -/
def WallRootCertificate.Check {n : ℕ} (c : WallRootCertificate n)
    (m : Finset (Fin 16)) : Prop :=
  ∀ cell ∈ m,
    (c.pose cell).DomainCheck cell ∧
      (c.ownership cell).Check cell (c.pose cell).owned 0 1

instance {n : ℕ} (c : WallRootCertificate n) (m : Finset (Fin 16)) :
    Decidable (c.Check m) := by
  unfold WallRootCertificate.Check
  infer_instance

/-- A wall root refines a uniform seed for an aligned owner assignment.  The
    closed-cell premise identifies the physical cell of each owner; the old
    state supplies the charted orientation.  The new owned points are proved
    strictly inside the square by the checked ownership tree, not inherited
    from the smaller conservative seed. -/
theorem WallRootCertificate.refine_uniform {n : ℕ} (hn : 0 < n)
    (c : WallRootCertificate n) (m : Finset (Fin 16)) (hm : m.card = 11)
    (hcheck : c.Check m) (P : Packing 11 coverCap)
    (hseed : StateHolds P (uniformSeedRoot n m))
    (hcell : ∀ i : Owner,
      ClosedCell (baselineRoles m i) (normalizeCenter (P.squares i).center)) :
    StateHolds P (c.root m) := by
  have hmem (i : Owner) : baselineRoles m i ∈ m := by
    have hi : baselineRoles m i ∈ Finset.univ.image (baselineRoles m) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [baselineRoles_image hm] at hi
    exact hi
  have hc (i : Owner) :
      (c.pose (baselineRoles m i)).DomainCheck (baselineRoles m i) ∧
        (c.ownership (baselineRoles m i)).Check
          (baselineRoles m i) (c.pose (baselineRoles m i)).owned 0 1 :=
    hcheck _ (hmem i)
  constructor
  · intro i
    obtain ⟨_, _, hrow⟩ := hseed.1 i
    obtain ⟨t, ht0, ht1, _, _, ha⟩ := hrow.2
    exact wall_seed_pose_cover hn (baselineRoles m i)
      (c.pose (baselineRoles m i)) (hc i).1 (P.squares i)
      (hcell i) (P.contained i) ⟨t, ht0, ht1, ha⟩
  · intro i
    obtain ⟨_, _, hrow⟩ := hseed.1 i
    obtain ⟨t, ht0, ht1, _, _, ha⟩ := hrow.2
    exact checked_wall_owned_hull (baselineRoles m i)
      (c.pose (baselineRoles m i)).owned
      (c.ownership (baselineRoles m i)) (hc i).2
      (P.squares i) (hcell i) (P.contained i) ⟨t, ht0, ht1, ha⟩

/-- The same checked data gives the public root-initialization contract.
    Relabeling is selected from actual occupancy before applying the
    state-preserving uniform-to-wall refinement. -/
theorem WallRootCertificate.initialized {n : ℕ} (hn : 0 < n)
    (c : WallRootCertificate n) (m : Finset (Fin 16))
    (hcheck : c.Check m) : RootValid m (c.root m) := by
  intro P hcharted hocc
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  have hseed : StateHolds (relabelPacking P perm) (uniformSeedRoot n m) := by
    constructor
    · intro i
      apply (uniformRows_contains n hn _ _).mpr
      exact ⟨baselineCellPolygon_contains (hcell i), hcharted (perm i)⟩
    · intro i
      exact hull_owned_of_vertices _ _ (baseline_seed_vertices_owned _ _ (hcell i))
  exact ⟨perm, c.refine_uniform hn m hm hcheck (relabelPacking P perm) hseed hcell⟩

end
end ElevenSquare.Tasks.T01.Handoff.GenericBridge

#print axioms ElevenSquare.Tasks.T01.Handoff.GenericBridge.WallRootCertificate.refine_uniform
#print axioms ElevenSquare.Tasks.T01.Handoff.GenericBridge.WallRootCertificate.initialized
