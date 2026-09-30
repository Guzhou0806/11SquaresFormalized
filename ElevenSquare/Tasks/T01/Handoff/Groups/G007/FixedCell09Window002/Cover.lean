import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.CoverLeaf008
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node007_checked : node007.Check nodeSource007 targets := by
  refine ⟨node008_checked, ?_⟩
  have he : baselineFlip ⟨(-108062499999753/132500000000000), (-1312499999997/4140625000000), (-30647730931063203190134032852913416953207269/15817187500000000000000000000000000000000000)⟩ :: nodeSource007 = nodeSource009 := by
    norm_num [baselineFlip, nodeSource007, nodeSource009]
  change node009.Check (baselineFlip ⟨(-108062499999753/132500000000000), (-1312499999997/4140625000000), (-30647730931063203190134032852913416953207269/15817187500000000000000000000000000000000000)⟩ :: nodeSource007) targets
  rw [he]
  exact node009_checked

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(669012187754229359304386036323/3820000000000000000000000000000), (669012187754229359304386036323/3820000000000000000000000000000), (571626731835400659049590617918828980108597677945742652401613989/773397200000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(669012187754229359304386036323/3820000000000000000000000000000), (669012187754229359304386036323/3820000000000000000000000000000), (571626731835400659049590617918828980108597677945742652401613989/773397200000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-122006054014052012680366981116127107760042777894121261/506150000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-122006054014052012680366981116127107760042777894121261/506150000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-96/265), (247/265), (250419074281881545738529/165625000000000000000000)⟩ :: nodeSource001 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource001, nodeSource007]
  change node007.Check (baselineFlip ⟨(-96/265), (247/265), (250419074281881545738529/165625000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node007_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-247/265), (-96/265), (-1838146710262545059381675264139753/1012300000000000000000000000000000)⟩ :: nodeSource000 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource000, nodeSource010]
  change node010.Check (baselineFlip ⟨(-247/265), (-96/265), (-1838146710262545059381675264139753/1012300000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node010_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002
