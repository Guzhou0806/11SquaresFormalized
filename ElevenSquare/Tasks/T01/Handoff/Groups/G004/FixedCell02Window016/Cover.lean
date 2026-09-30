import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node006_checked : node006.Check nodeSource006 targets := by
  refine ⟨node007_checked, ?_⟩
  have he : baselineFlip ⟨(-11132499999975479/16693984375000000), (2304427499994924153/3739452500000000000), (-16397900336295455805463776753494499/18339022950500000000000000000000000)⟩ :: nodeSource006 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource006, nodeSource008]
  change node008.Check (baselineFlip ⟨(-11132499999975479/16693984375000000), (2304427499994924153/3739452500000000000), (-16397900336295455805463776753494499/18339022950500000000000000000000000)⟩ :: nodeSource006) targets
  rw [he]
  exact node008_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (4027292993549998588452980965775760181176119709253463326985394481549/4365406932880000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (4027292993549998588452980965775760181176119709253463326985394481549/4365406932880000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(224/305), (-207/305), (459756628042989027262613501500587139/357117713750000000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(224/305), (-207/305), (459756628042989027262613501500587139/357117713750000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(207/305), (224/305), (13841664786225919848842834882647059927/5713883420000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(207/305), (224/305), (13841664786225919848842834882647059927/5713883420000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016
