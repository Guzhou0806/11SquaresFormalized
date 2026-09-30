import ElevenSquare.Tasks.T01.Wall

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- A valid but weak rational wall margin in Lean's normalized coordinates.
The archived physical margin must be divided by its square side to recover
the exact first-bin boundary `1/2`; see `SampleWallRow00`. -/
def wallMargin : ℚ := 191000000000000000000 / 387708359002281417731

/-- Both endpoints of the closed first angular bin pass the exact wall bound. -/
theorem wall_margin_check : BaselineWallCheck 0 (1/32) wallMargin := by
  norm_num [BaselineWallCheck, wallMargin]

/-- The two lower wall inequalities are direct members of the checked slab. -/
theorem lower_x_check :
    BaselineImplicationCheck (baselineSlab (0 : Fin 16) wallMargin)
      ⟨-1, 0, -wallMargin⟩ [(0, 1)] := by
  constructor
  · intro iw hi
    simp only [List.mem_singleton] at hi
    subst iw
    constructor
    · simp [baselineSlab]
    · norm_num
  · simp [baselineCombinationSum, baselineSlab, baselineZeroHalfplane]

theorem lower_y_check :
    BaselineImplicationCheck (baselineSlab (0 : Fin 16) wallMargin)
      ⟨0, -1, -wallMargin⟩ [(2, 1)] := by
  constructor
  · intro iw hi
    simp only [List.mem_singleton] at hi
    subst iw
    constructor
    · simp [baselineSlab]
    · norm_num
  · simp [baselineCombinationSum, baselineSlab, baselineZeroHalfplane]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.wall_margin_check
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.lower_x_check
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.lower_y_check
