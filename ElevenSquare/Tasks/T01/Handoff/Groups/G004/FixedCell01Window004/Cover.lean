import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window004.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window004.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window004
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-4047/4145), (-896/4145), (-56568541661522515526567627861430658956829/34930794693350000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-4047/4145), (-896/4145), (-56568541661522515526567627861430658956829/34930794693350000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window004
