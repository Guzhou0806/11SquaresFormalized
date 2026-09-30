import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.CoverLeaf008
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node007_checked : node007.Check nodeSource007 targets := by
  refine ⟨node008_checked, ?_⟩
  have he : baselineFlip ⟨(-5248/5777), (2415/5777), (-1419068517036252089280001/3610625000000000000000000)⟩ :: nodeSource007 = nodeSource009 := by
    norm_num [baselineFlip, nodeSource007, nodeSource009]
  change node009.Check (baselineFlip ⟨(-5248/5777), (2415/5777), (-1419068517036252089280001/3610625000000000000000000)⟩ :: nodeSource007) targets
  rw [he]
  exact node009_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(233953124999517/577700000000000), (19859374999959/22566406250000), (6740737328943410404687797777/2888500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(233953124999517/577700000000000), (19859374999959/22566406250000), (6740737328943410404687797777/2888500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(19859374999959/22566406250000), (-233953124999517/577700000000000), (1944959727816780114896595777/2888500000000000000000000000)⟩ :: nodeSource004 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource004, nodeSource010]
  change node010.Check (baselineFlip ⟨(19859374999959/22566406250000), (-233953124999517/577700000000000), (1944959727816780114896595777/2888500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node010_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-19859374999959/22566406250000), (233953124999517/577700000000000), (-644550283595413145420891972428963873164254691/2206814000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-19859374999959/22566406250000), (233953124999517/577700000000000), (-644550283595413145420891972428963873164254691/2206814000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-233953124999517/577700000000000), (-19859374999959/22566406250000), (-204190895164453496498713617456798113548780593/86203671875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-233953124999517/577700000000000), (-19859374999959/22566406250000), (-204190895164453496498713617456798113548780593/86203671875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017
