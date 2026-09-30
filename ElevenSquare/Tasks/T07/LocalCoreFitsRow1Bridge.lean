import ElevenSquare.Tasks.T07.LocalCoreFitsRow1C4
import ElevenSquare.Tasks.T07.LocalFieldPullback

/-! The compact core check and source polygon as one actual physical pose row. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def terminal1PhysicalPoseRow : PoseRow :=
  fieldPoseRow (1/7936) (1/3968) terminal1Domain

theorem terminal1PhysicalPoseRow_source (q : UnitSquare)
    (hq : terminal1PhysicalPoseRow.contains q) :
    toField q.center ∈ terminal1Domain.carrier :=
  fieldPoseRow_source _ _ _ q hq

theorem terminal1PhysicalPoseRow_coreFits (q : UnitSquare)
    (hq : terminal1PhysicalPoseRow.contains q) :
    CoreFits (rationalHull (terminal1CoreField.map qpointFieldNormalize)) q := by
  obtain ⟨_, t, _, _, htlo, hthi, haxis⟩ := hq
  have hlo : (1/7936 : ℝ) ≤ t := by
    simpa [terminal1PhysicalPoseRow, fieldPoseRow] using htlo
  have hhi : t ≤ (1/3968 : ℝ) := by
    simpa [terminal1PhysicalPoseRow, fieldPoseRow] using hthi
  exact terminal1_coreFits_c4 q t hlo hhi haxis

end
end ElevenSquare.Tasks.T07
