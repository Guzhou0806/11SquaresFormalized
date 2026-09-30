import ElevenSquare.Tasks.T02.Prior1000Step000Row029.SharedCoreInteger.Data
import ElevenSquare.Tasks.T02.RationalChecks

namespace ElevenSquare.Tasks.T02.Prior1000Step000Row029.SharedCoreInteger
open ElevenSquare.Pending ElevenSquare.Tasks.T02
open IntegerCover
noncomputable section

set_option maxRecDepth 100000
theorem source_normalized : PolygonNormalizationCheck inputPolygon source := by rational_decide
theorem targets_normalized : TargetsNormalizationCheck certificate.targets targets := by rational_decide

end
end ElevenSquare.Tasks.T02.Prior1000Step000Row029.SharedCoreInteger
