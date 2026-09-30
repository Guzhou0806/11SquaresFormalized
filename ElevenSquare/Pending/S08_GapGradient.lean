import ElevenSquare.Pending.S08_GapDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ElevenSquare.Pending
noncomputable section

def gapGradient (S : ℝ) (q₀ : Owner → UnitSquare) (g : Gap) (j : Fin 33) : ℝ :=
  deriv (fun t : ℝ => gapValue S q₀ g (Function.update (fun _ => 0) j t)) 0

end
end ElevenSquare.Pending
