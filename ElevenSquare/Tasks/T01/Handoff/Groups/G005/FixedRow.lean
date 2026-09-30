import ElevenSquare.Tasks.T01.Handoff.Groups.G005.Support
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedFeatureRow

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005
open ElevenSquare.Pending
noncomputable section

def fixedFeatures : Fin 2 → Finset QPoint := ![featureA, featureB]
def fixedThresholds : Fin 2 → ℕ := ![3, 2]

theorem captureChoice_of_fixedFeature (q : UnitSquare) (f : Fin 2)
    (h : BaselineMajorityCapture (fixedFeatures f) (fixedThresholds f) q) :
    CaptureChoice q := by
  fin_cases f
  · exact Or.inl h
  · exact Or.inr h

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.captureChoice_of_fixedFeature
