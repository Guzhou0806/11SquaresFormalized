import ElevenSquare.Tasks.T06.CertificateBlock00
import ElevenSquare.Tasks.T06.CertificateBlock01
import ElevenSquare.Tasks.T06.CertificateBlock02
import ElevenSquare.Tasks.T06.CertificateBlock03
import ElevenSquare.Tasks.T06.CertificateBlock04
import ElevenSquare.Tasks.T06.CertificateBlock05
import ElevenSquare.Tasks.T06.CertificateBlock06
import ElevenSquare.Tasks.T06.CertificateBlock07

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlocks (q : Fin 8) (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex q r) j s
      (dualNumerators (certificateBlockIndex q r) j s) ∧
    integerMassCheck (certificateBlockIndex q r) j s
      (dualNumerators (certificateBlockIndex q r) j s) := by
  fin_cases q
  · exact certificateBlock00 r j s
  · exact certificateBlock01 r j s
  · exact certificateBlock02 r j s
  · exact certificateBlock03 r j s
  · exact certificateBlock04 r j s
  · exact certificateBlock05 r j s
  · exact certificateBlock06 r j s
  · exact certificateBlock07 r j s

theorem allIntegerChecks (b : Fin 128) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck b j s (dualNumerators b j s) ∧
    integerMassCheck b j s (dualNumerators b j s) := by
  let q : Fin 8 := ⟨b.val / 16, by have hb := b.isLt; omega⟩
  let r : Fin 16 := ⟨b.val % 16, Nat.mod_lt _ (by decide)⟩
  have hb : certificateBlockIndex q r = b := by
    apply Fin.ext
    dsimp [certificateBlockIndex, q, r]
    omega
  rw [← hb]
  exact certificateBlocks q r j s

theorem allIntegerResidualChecks (b : Fin 128) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck b j s (dualNumerators b j s) := (allIntegerChecks b j s).1

theorem allIntegerMassChecks (b : Fin 128) (j : Fin 33) (s : Fin 2) :
    integerMassCheck b j s (dualNumerators b j s) := (allIntegerChecks b j s).2

end ElevenSquare.Tasks.T06
