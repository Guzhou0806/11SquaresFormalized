import ElevenSquare.Tasks.T07.CaptureBranches

/-! The four closed cuts preserve the starting state, including its owned
hulls. This is shared by conservative and strict-owned semantic roots. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def seedFar15 (s : PoseState) (i15 : Owner) : PoseState :=
  cutYUpper s i15 physicalYCut

def seedFar13 (s : PoseState) (i15 i13 : Owner) : PoseState :=
  cutAngleUpper (cutYLower s i15 physicalYCut) i13 (147/512)

def seedFar2 (s : PoseState) (i15 i13 i2 : Owner) : PoseState :=
  cutAngleUpper
    (cutAngleLower (cutYLower s i15 physicalYCut) i13 (147/512))
    i2 (183/512)

def seedNear (s : PoseState) (i15 i13 i2 : Owner) : PoseState :=
  cutAngleLower
    (cutAngleLower (cutYLower s i15 physicalYCut) i13 (147/512))
    i2 (183/512)

/-- This branch coverage preserves any seeded pose rows and owned hulls. No strict
inequality is introduced at a cut, so equalities remain represented. -/
theorem state_closed_branch_states {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) (hchart : IsCharted P)
    (i15 i13 i2 : Owner) :
    StateHolds P (seedFar15 s i15) ∨
      StateHolds P (seedFar13 s i15 i13) ∨
      StateHolds P (seedFar2 s i15 i13 i2) ∨
      StateHolds P (seedNear s i15 i13 i2) := by
  obtain ⟨t13, ht13₀, ht13₁, ha13⟩ := hchart i13
  obtain ⟨t2, ht2₀, ht2₁, ha2⟩ := hchart i2
  let y15 : ℝ := (P.squares i15).center.2-coverCap/2
  have cast147 : ((147/512 : ℚ) : ℝ) = 147/512 := by norm_num
  have cast183 : ((183/512 : ℚ) : ℝ) = 183/512 := by norm_num
  have hroot : StateHolds P s := hs
  have yupper (h : y15 ≤ 5/4) :
      StateHolds P (cutYUpper s i15 physicalYCut) := by
    apply cutYUpper_sound P s i15 physicalYCut hroot
    rw [physicalYCut_eq]
    dsimp [y15] at h
    linarith
  have ylower (h : 5/4 ≤ y15) :
      StateHolds P (cutYLower s i15 physicalYCut) := by
    apply cutYLower_sound P s i15 physicalYCut hroot
    rw [physicalYCut_eq]
    dsimp [y15] at h
    linarith
  rcases capture_closed_partition y15 t13 t2 with h15 | h13 | h2 | hnear
  · exact Or.inl (yupper h15)
  · rcases h13 with ⟨hy, ht⟩
    exact Or.inr (Or.inl
      (cutAngleUpper_from_parameter P _ i13 (147/512) (ylower hy)
        t13 ht13₀ ha13 (by simpa only [cast147] using ht)))
  · rcases h2 with ⟨hy, ht13, ht2⟩
    have hfirst := cutAngleLower_from_parameter P _ i13 (147/512)
      (ylower hy) t13 ht13₀ ha13 (by simpa only [cast147] using ht13)
    exact Or.inr (Or.inr (Or.inl
      (cutAngleUpper_from_parameter P _ i2 (183/512)
        hfirst t2 ht2₀ ha2 (by simpa only [cast183] using ht2))))
  · rcases hnear with ⟨hy, ht13, ht2⟩
    have hfirst := cutAngleLower_from_parameter P _ i13 (147/512)
      (ylower hy) t13 ht13₀ ha13 (by simpa only [cast147] using ht13)
    exact Or.inr (Or.inr (Or.inr
      (cutAngleLower_from_parameter P _ i2 (183/512)
        hfirst t2 ht2₀ ha2 (by simpa only [cast183] using ht2))))

end
end ElevenSquare.Tasks.T07
