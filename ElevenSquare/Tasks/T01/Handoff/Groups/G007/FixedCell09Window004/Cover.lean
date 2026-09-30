import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-9465435689808419456483045548717962318580285674143927569/43328350000000000000000000000000000000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-9465435689808419456483045548717962318580285674143927569/43328350000000000000000000000000000000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(-2688/4537), (3655/4537), (2563382813150166046016439/2835625000000000000000000)⟩ :: nodeSource004 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource004, nodeSource008]
  change node008.Check (baselineFlip ⟨(-2688/4537), (3655/4537), (2563382813150166046016439/2835625000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node008_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-10171874999979/17722656250000), (354078124999269/453700000000000), (2040106914698085159819103587224254199742546213/1733134000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-10171874999979/17722656250000), (354078124999269/453700000000000), (2040106914698085159819103587224254199742546213/1733134000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-354078124999269/453700000000000), (-10171874999979/17722656250000), (-161296520131242165479581337319993286704482133/67700546875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-354078124999269/453700000000000), (-10171874999979/17722656250000), (-161296520131242165479581337319993286704482133/67700546875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004
