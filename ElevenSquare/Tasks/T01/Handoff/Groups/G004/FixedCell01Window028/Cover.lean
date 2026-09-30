import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window028.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window028.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window028.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window028
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-126464/126545), (4527/126545), (-2748380640654932991688791360858201118749579071/1935515085044725900000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-126464/126545), (4527/126545), (-2748380640654932991688791360858201118749579071/1935515085044725900000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-4527/126545), (-126464/126545), (-1094154669633099654048849275334645422450606703/1935515085044725900000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-4527/126545), (-126464/126545), (-1094154669633099654048849275334645422450606703/1935515085044725900000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window028
