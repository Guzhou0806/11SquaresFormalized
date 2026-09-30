import ElevenSquare.Tasks.T07.NearCenterPacket
import ElevenSquare.Tasks.T07.GeometryCaptureInterface

/-! The checked final-state packet enters the focused local rectangle. The
outer trace still has to prove `FinalNearRowsHold`; this theorem makes that
semantic dependency explicit. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem finalNearRows_to_focused_rectangle
    (Q : Packing 11 coverCap) (hfinal : FinalNearRowsHold Q) :
    ∃ (q : Owner → UnitSquare) (θ : Owner → ℝ),
      (∀ i, SameSquare (quarterSquare coverCap T (Q.squares i)) (q i)) ∧
      (∀ i, (q i).center = fieldToLocal (toField (Q.squares i).center)) ∧
      InRectangle focusedRadii (poseDisplacementWithAngles q θ) ∧
      (∀ i, (q i).center =
          perturbedCenter constructionSquare (poseDisplacementWithAngles q θ) i ∧
        (q i).axis =
          perturbedAxis constructionSquare (poseDisplacementWithAngles q θ) i) := by
  classical
  choose row hrow t _ht0 _ht1 htlo hthi haxis P hP hpoly using hfinal
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
    have hf : InFinalNearCenter i (toField (Q.squares i).center) :=
      ⟨row i, hrow i, P i, hP i, hpoly i⟩
    have hb := finalNear_centers_in_focused_radii i
      (toField (Q.squares i).center) hf
    simpa only [hcenter i, constructionSquare] using hb
  have hangles (i : Owner) : |θ i| ≤ focusedRadii (coordinate i 2) := by
    exact near_angle_in_focused_radius i (t i)
      ⟨row i, hrow i, htlo i, hthi i⟩
  have haxis' (i : Owner) :
      (q i).axis = rotateAxis (θ i) (constructionSquare i).axis := by
    exact near_quarterChart_rotates i (Q.squares i) (t i) (haxis i)
  refine ⟨q, θ, hsame, hcenter, poseWithAngles_inRectangle q θ hbounds hangles, ?_⟩
  exact poseWithAngles_represents q θ haxis'

/-- A near final-state packing contained in a centered square of side `S ≤ T`
becomes a physical local packing whose 33 recorded deviations satisfy the
focused rectangle. The near trace ancestry is precisely `hfinal`. -/
theorem finalNearRows_to_local_packing
    (Q : Packing 11 coverCap) (S : ℝ)
    (hsmall : CenteredPacking Q S) (hST : S ≤ T)
    (hfinal : FinalNearRowsHold Q) :
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
    finalNearRows_to_focused_rectangle Q hfinal
  let B : Packing 11 T := quarterPacking Q T_pos.le hsmall hST
  have hs (i : Owner) : SameSquare (B.squares i) (q i) := hsame i
  let R : Packing 11 T := replaceSquares B q hs
  refine ⟨R, θ, ?_, ?_, ?_⟩
  · exact replaceSquares_centered B q hs (quarterPacking_centered Q T_pos.le hsmall hST)
  · exact hrectangle
  · exact hrep

end
end ElevenSquare.Tasks.T07
