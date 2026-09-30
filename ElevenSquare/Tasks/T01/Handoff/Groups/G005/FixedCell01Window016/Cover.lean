import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window016.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window016.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window016
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-16215/16553), (-3328/16553), (-1822840761599410847353891353702968679369133/1097831916558860000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-16215/16553), (-3328/16553), (-1822840761599410847353891353702968679369133/1097831916558860000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window016
