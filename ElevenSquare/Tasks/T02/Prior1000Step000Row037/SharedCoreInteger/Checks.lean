import ElevenSquare.Tasks.T02.Prior1000Step000Row037.SharedCoreInteger.Normalization

namespace ElevenSquare.Tasks.T02.Prior1000Step000Row037.SharedCoreInteger
open ElevenSquare.Pending ElevenSquare.Tasks.T02
open IntegerCover
noncomputable section

set_option maxRecDepth 100000
theorem integer_checked : integerCover.Check source.poly (targets.map NormalizedPoly.poly) := by decide
theorem coverage_checked : integerCertificate.Check inputPolygon certificate.targets :=
  ⟨source_normalized, targets_normalized, integer_checked⟩
theorem coverage_sound (p : Point) (hp : p ∈ inputPolygon.carrier) :
    ∃ t ∈ certificate.targets, p ∈ t.carrier :=
  rational_certificate_sound _ _ integerCertificate coverage_checked p hp

end
end ElevenSquare.Tasks.T02.Prior1000Step000Row037.SharedCoreInteger
