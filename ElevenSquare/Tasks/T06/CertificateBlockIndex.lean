import ElevenSquare.Tasks.T06.DataPacket
import Lean.Elab.Tactic.Omega

namespace ElevenSquare.Tasks.T06

/-- A small product index used to assemble the independently checked branches. -/
def certificateBlockIndex (q : Fin 8) (r : Fin 16) : Fin 128 :=
  ⟨16 * q.val + r.val, by have hq := q.isLt; have hr := r.isLt; omega⟩

end ElevenSquare.Tasks.T06
