import ElevenSquare.Tasks.T07.CaptureCuts
import ElevenSquare.Tasks.T07.CapturePartition

/-! The four closed case-438 branch predicates give four sound semantic
starting states. The square indices are supplied by the owner permutation. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def physicalYCut : ℚ :=
  (387708359002281417731 : ℚ) / 100000000000000000000 / 2 + 5/4

theorem physicalYCut_eq : (physicalYCut : ℝ) = coverCap/2 + 5/4 := by
  norm_num [physicalYCut, coverCap]

def far15State (i15 : Owner) : PoseState :=
  cutYUpper chartRoot i15 physicalYCut

def far13State (i15 i13 : Owner) : PoseState :=
  cutAngleUpper (cutYLower chartRoot i15 physicalYCut) i13 (147/512)

def far2State (i15 i13 i2 : Owner) : PoseState :=
  cutAngleUpper
    (cutAngleLower (cutYLower chartRoot i15 physicalYCut) i13 (147/512))
    i2 (183/512)

def nearState (i15 i13 i2 : Owner) : PoseState :=
  cutAngleLower
    (cutAngleLower (cutYLower chartRoot i15 physicalYCut) i13 (147/512))
    i2 (183/512)

/-- This is semantic branch coverage for *every* charted packing. No strict
inequality is introduced at a cut, so equalities remain represented. -/
theorem charted_closed_branch_states {S : ℝ} (P : Packing 11 S)
    (hchart : IsCharted P) (i15 i13 i2 : Owner) :
    StateHolds P (far15State i15) ∨
      StateHolds P (far13State i15 i13) ∨
      StateHolds P (far2State i15 i13 i2) ∨
      StateHolds P (nearState i15 i13 i2) := by
  obtain ⟨t13, ht13₀, ht13₁, ha13⟩ := hchart i13
  obtain ⟨t2, ht2₀, ht2₁, ha2⟩ := hchart i2
  let y15 : ℝ := (P.squares i15).center.2-coverCap/2
  have cast147 : ((147/512 : ℚ) : ℝ) = 147/512 := by norm_num
  have cast183 : ((183/512 : ℚ) : ℝ) = 183/512 := by norm_num
  have hroot : StateHolds P chartRoot := chartRoot_holds P hchart
  have yupper (h : y15 ≤ 5/4) :
      StateHolds P (cutYUpper chartRoot i15 physicalYCut) := by
    apply cutYUpper_sound P chartRoot i15 physicalYCut hroot
    rw [physicalYCut_eq]
    dsimp [y15] at h
    linarith
  have ylower (h : 5/4 ≤ y15) :
      StateHolds P (cutYLower chartRoot i15 physicalYCut) := by
    apply cutYLower_sound P chartRoot i15 physicalYCut hroot
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

/-- Once concrete Lean traces for the three far branches are supplied,
semantic soundness leaves every charted packing in the near branch. -/
theorem near_of_far_terminal_traces {S : ℝ} (P : Packing 11 S)
    (hchart : IsCharted P) (i15 i13 i2 : Owner)
    (far15 : ∃ s, VerifiedTrace (far15State i15) s ∧ Terminal s)
    (far13 : ∃ s, VerifiedTrace (far13State i15 i13) s ∧ Terminal s)
    (far2 : ∃ s, VerifiedTrace (far2State i15 i13 i2) s ∧ Terminal s) :
    StateHolds P (nearState i15 i13 i2) := by
  rcases charted_closed_branch_states P hchart i15 i13 i2 with h | h | h | h
  · obtain ⟨s, trace, terminal⟩ := far15
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far13
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · obtain ⟨s, trace, terminal⟩ := far2
    exact (terminal_contradiction P s (verified_trace_sound P h trace) terminal).elim
  · exact h

end
end ElevenSquare.Tasks.T07
