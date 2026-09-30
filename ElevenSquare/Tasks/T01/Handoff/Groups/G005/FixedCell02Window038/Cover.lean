import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window038.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window038.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window038.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window038
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-842471499998203457/13937696500000000000), (-81529499999826141/87110603125000000), (-538225028810879458808922991245123471/807731325264500000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(-842471499998203457/13937696500000000000), (-81529499999826141/87110603125000000), (-538225028810879458808922991245123471/807731325264500000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(480/481), (-31/481), (255944911991301145425688804307296098689/106484001260000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(480/481), (-31/481), (255944911991301145425688804307296098689/106484001260000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window038
