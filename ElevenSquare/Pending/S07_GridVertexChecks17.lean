import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.GridDistance

theorem vertex_check272 : pointCheck rationalPoint272 gridPoint272 = true := by
  have h := fractionCheck_sound 1 1 1 1 1048576 1048576 (by decide)
  simpa only [rationalPoint272, gridPoint272, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one, zero_div] using h

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.vertex_check272
