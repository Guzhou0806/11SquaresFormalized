import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(-995207499997893777/2522296070312500000), (5544727499988265329/6457077940000000000), (8045330022135178059760227752255456433/48571593107216500000000000000000000000)⟩ :: nodeSource004 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource004, nodeSource006]
  change node006.Check (baselineFlip ⟨(-995207499997893777/2522296070312500000), (5544727499988265329/6457077940000000000), (8045330022135178059760227752255456433/48571593107216500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(448/1073), (-975/1073), (1304962515971294574922291058983093873/3083254716350000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(448/1073), (-975/1073), (1304962515971294574922291058983093873/3083254716350000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(975/1073), (448/1073), (318564299817115932396208547703692954361/123330188654000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(975/1073), (448/1073), (318564299817115932396208547703692954361/123330188654000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014
