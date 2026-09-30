import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node008_checked : node008.Check nodeSource008 targets := by
  refine ⟨node009_checked, ?_⟩
  have he : baselineFlip ⟨(-1728/1753), (295/1753), (-1111311513829657046710621/1095625000000000000000000)⟩ :: nodeSource008 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource008, nodeSource010]
  change node010.Check (baselineFlip ⟨(-1728/1753), (295/1753), (-1111311513829657046710621/1095625000000000000000000)⟩ :: nodeSource008) targets
  rw [he]
  exact node010_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-12656249999973/13695312500000), (27656249999941/175300000000000), (-683430380500613733938262247/876500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-12656249999973/13695312500000), (27656249999941/175300000000000), (-683430380500613733938262247/876500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(27656249999941/175300000000000), (12656249999973/13695312500000), (1751503618020129240198215753/876500000000000000000000000)⟩ :: nodeSource004 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource004, nodeSource008]
  change node008.Check (baselineFlip ⟨(27656249999941/175300000000000), (12656249999973/13695312500000), (1751503618020129240198215753/876500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node008_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-12656249999973/13695312500000), (27656249999941/175300000000000), (-658925448227942678060156035530418513750882043/669646000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-12656249999973/13695312500000), (27656249999941/175300000000000), (-658925448227942678060156035530418513750882043/669646000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-27656249999941/175300000000000), (-12656249999973/13695312500000), (-105788931617136841837661215703340820971052921/52316093750000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-27656249999941/175300000000000), (-12656249999973/13695312500000), (-105788931617136841837661215703340820971052921/52316093750000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021
