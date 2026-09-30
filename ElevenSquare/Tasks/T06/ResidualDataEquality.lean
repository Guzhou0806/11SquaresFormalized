import ElevenSquare.Tasks.T06.DataPacket

/-! The packet uses the exact scaled integer residual proposals directly. -/
namespace ElevenSquare.Tasks.T06

theorem allResidualData (b : Fin 128) (j : Fin 33) (s : Fin 2) :
    residualBounds b j s =
      (residualNumerators b j s : ℚ) / 1000000000000000000000000 := rfl

end ElevenSquare.Tasks.T06
