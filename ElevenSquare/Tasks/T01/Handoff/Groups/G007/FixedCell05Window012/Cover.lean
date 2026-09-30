import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node008_checked : node008.Check nodeSource008 targets := by
  refine ⟨node009_checked, ?_⟩
  have he : baselineFlip ⟨(-5687499999987/6640625000000), (38062499999913/212500000000000), (-6776079262321949318828943/8500000000000000000000000)⟩ :: nodeSource008 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource008, nodeSource010]
  change node010.Check (baselineFlip ⟨(-5687499999987/6640625000000), (38062499999913/212500000000000), (-6776079262321949318828943/8500000000000000000000000)⟩ :: nodeSource008) targets
  rw [he]
  exact node010_checked

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-44156608194619922257349227673639281661987122207548329/162350000000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-44156608194619922257349227673639281661987122207548329/162350000000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-81199080627709700062922296002654145719515826692434179/649400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-81199080627709700062922296002654145719515826692434179/649400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-416/425), (87/425), (-256376795501458067439491/265625000000000000000000)⟩ :: nodeSource001 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource001, nodeSource007]
  change node007.Check (baselineFlip ⟨(-416/425), (87/425), (-256376795501458067439491/265625000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node007_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-87/425), (-416/425), (-133538172462042289717211467503549/81175000000000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-87/425), (-416/425), (-133538172462042289717211467503549/81175000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012
