import ElevenSquare.Tasks.T07.NearStateBridge

/-! Native trace-state handoff for the near case. The packing is indexed by
construction role: role 0 is source cell 3, role 1 is source cell 15, etc.
The source-cell map records this finite relabeling explicitly. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def nearSourceCell : Owner → Fin 16 :=
  ![(3 : Fin 16), 15, 8, 0, 4, 1, 2, 11, 9, 10, 13]

theorem nearSourceCell_injective : Function.Injective nearSourceCell := by
  decide

/-- The exact 136 angular rows and 11 rational field boxes, expressed as
native `StateHolds`, give the full 33-coordinate focused displacement. -/
theorem nearOuterState_to_focused_rectangle
    (Q : Packing 11 coverCap) (hs : StateHolds Q nearOuterState) :
    ∃ (q : Owner → UnitSquare) (θ : Owner → ℝ),
      (∀ i, SameSquare (quarterSquare coverCap T (Q.squares i)) (q i)) ∧
      (∀ i, (q i).center = fieldToLocal (toField (Q.squares i).center)) ∧
      InRectangle focusedRadii (poseDisplacementWithAngles q θ) ∧
      (∀ i, (q i).center =
          perturbedCenter constructionSquare (poseDisplacementWithAngles q θ) i ∧
        (q i).axis =
          perturbedAxis constructionSquare (poseDisplacementWithAngles q θ) i) := by
  classical
  have hfinal := (nearOuterState_iff Q).mp hs
  choose row hrow t _ht0 _ht1 htlo hthi haxis hbox using hfinal
  let q : Owner → UnitSquare := fun i =>
    quarterChartSquare coverCap T (Q.squares i) (nearOneBranch i (t i))
  let θ : Owner → ℝ := fun i => nearAngleDisplacement i (t i)
  have hsame (i : Owner) :
      SameSquare (quarterSquare coverCap T (Q.squares i)) (q i) := by
    exact quarterChartSquare_same coverCap T (Q.squares i) _
  have hcenter (i : Owner) :
      (q i).center = fieldToLocal (toField (Q.squares i).center) := by
    rw [show (q i).center = quarterTo coverCap T (Q.squares i).center by
      exact quarterChartSquare_center coverCap T (Q.squares i) _]
    exact (fieldToLocal_toField _).symm
  have hbounds (i : Owner) :
      |(q i).center.1-(constructionSquare i).center.1| ≤
          focusedRadii (coordinate i 0) ∧
      |(q i).center.2-(constructionSquare i).center.2| ≤
          focusedRadii (coordinate i 1) := by
    have hb := nearBox_center_in_focused_radii i
      (toField (Q.squares i).center) (hbox i)
    simpa only [hcenter i, constructionSquare] using hb
  have hangles (i : Owner) : |θ i| ≤ focusedRadii (coordinate i 2) := by
    exact near_angle_in_focused_radius i (t i)
      ⟨row i, hrow i, htlo i, hthi i⟩
  have haxis' (i : Owner) :
      (q i).axis = rotateAxis (θ i) (constructionSquare i).axis := by
    exact near_quarterChart_rotates i (Q.squares i) (t i) (haxis i)
  exact ⟨q, θ, hsame, hcenter,
    poseWithAngles_inRectangle q θ hbounds hangles,
    poseWithAngles_represents q θ haxis'⟩

/-- A centered cap packing satisfying the native outer-state near packet
is a physical focused local packing after the exact quarter-turn transport. -/
theorem nearOuterState_to_local_packing
    (Q : Packing 11 coverCap) (S : ℝ)
    (hsmall : CenteredPacking Q S) (hST : S ≤ T)
    (hs : StateHolds Q nearOuterState) :
    ∃ (R : Packing 11 T) (θ : Owner → ℝ),
      CenteredPacking R S ∧
      InRectangle focusedRadii (poseDisplacementWithAngles R.squares θ) ∧
      (∀ i, (R.squares i).center =
          perturbedCenter constructionSquare
            (poseDisplacementWithAngles R.squares θ) i ∧
        (R.squares i).axis =
          perturbedAxis constructionSquare
            (poseDisplacementWithAngles R.squares θ) i) := by
  obtain ⟨q, θ, hsame, _, hrectangle, hrep⟩ :=
    nearOuterState_to_focused_rectangle Q hs
  let B : Packing 11 T := quarterPacking Q T_pos.le hsmall hST
  have hmatch (i : Owner) : SameSquare (B.squares i) (q i) := hsame i
  let R : Packing 11 T := replaceSquares B q hmatch
  exact ⟨R, θ,
    replaceSquares_centered B q hmatch (quarterPacking_centered Q T_pos.le hsmall hST),
    hrectangle, hrep⟩

/-- A genuine final trace may retain its promoted owned hulls. Its rows only
need to lie in the checked final near packet; ownership is not discarded. -/
theorem nearSubsumedState_to_local_packing
    (Q : Packing 11 coverCap) (S : ℝ) (s : PoseState)
    (hs : StateHolds Q s) (hsub : NearRowsSubsumed s)
    (hsmall : CenteredPacking Q S) (hST : S ≤ T) :
    ∃ (R : Packing 11 T) (θ : Owner → ℝ),
      CenteredPacking R S ∧
      InRectangle focusedRadii (poseDisplacementWithAngles R.squares θ) ∧
      (∀ i, (R.squares i).center =
          perturbedCenter constructionSquare
            (poseDisplacementWithAngles R.squares θ) i ∧
        (R.squares i).axis =
          perturbedAxis constructionSquare
            (poseDisplacementWithAngles R.squares θ) i) :=
  nearOuterState_to_local_packing Q S hsmall hST
    (stateHolds_nearOuterState_of_subsumed Q s hs hsub)

/-- The remaining source obligation is a concrete capture trace from an
occupied seed, followed by row inclusion in the finite near packet. -/
theorem nearVerifiedTrace_to_local_packing
    (Q : Packing 11 coverCap) (S : ℝ) (seed finalState : PoseState)
    (hseed : StateHolds Q seed)
    (trace : VerifiedTrace seed finalState)
    (hsub : NearRowsSubsumed finalState)
    (hsmall : CenteredPacking Q S) (hST : S ≤ T) :
    ∃ (R : Packing 11 T) (θ : Owner → ℝ),
      CenteredPacking R S ∧
      InRectangle focusedRadii (poseDisplacementWithAngles R.squares θ) ∧
      (∀ i, (R.squares i).center =
          perturbedCenter constructionSquare
            (poseDisplacementWithAngles R.squares θ) i ∧
        (R.squares i).axis =
          perturbedAxis constructionSquare
            (poseDisplacementWithAngles R.squares θ) i) :=
  nearSubsumedState_to_local_packing Q S finalState
    (verified_trace_sound Q hseed trace) hsub hsmall hST

end
end ElevenSquare.Tasks.T07
