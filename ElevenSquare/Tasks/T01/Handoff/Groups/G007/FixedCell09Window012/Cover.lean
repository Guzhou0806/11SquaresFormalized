import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(-17664/21145), (11623/21145), (-93843132185543073363889/13215625000000000000000000)⟩ :: nodeSource004 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource004, nodeSource006]
  change node006.Check (baselineFlip ⟨(-17664/21145), (11623/21145), (-93843132185543073363889/13215625000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-33960937499931/41298828125000), (5720695312488377/10572500000000000), (6163177629454277968325537079225030552818737529/40386950000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-33960937499931/41298828125000), (5720695312488377/10572500000000000), (6163177629454277968325537079225030552818737529/40386950000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-5720695312488377/10572500000000000), (-33960937499931/41298828125000), (-24479391395015733031474919224659564588130957/9860095214843750000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-5720695312488377/10572500000000000), (-33960937499931/41298828125000), (-24479391395015733031474919224659564588130957/9860095214843750000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012
