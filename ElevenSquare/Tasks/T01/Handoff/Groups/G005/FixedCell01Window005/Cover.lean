import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window005.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window005.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-262063/262225), (-9216/262225), (-1652003451973763984720330113223655163144400789/1080356038989755500000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-262063/262225), (-9216/262225), (-1652003451973763984720330113223655163144400789/1080356038989755500000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window005
