import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node008_checked : node008.Check nodeSource008 targets := by
  refine ⟨node009_checked, ?_⟩
  have he : baselineFlip ⟨(-1453124999997/3375781250000), (1875015624996129/2160500000000000), (1293824183001298394731056321/2160500000000000000000000000)⟩ :: nodeSource008 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource008, nodeSource010]
  change node010.Check (baselineFlip ⟨(-1453124999997/3375781250000), (1875015624996129/2160500000000000), (1293824183001298394731056321/2160500000000000000000000000)⟩ :: nodeSource008) targets
  rw [he]
  exact node010_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(1875015624996129/2160500000000000), (1453124999997/3375781250000), (4825448402794460424567597321/2160500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(1875015624996129/2160500000000000), (1453124999997/3375781250000), (4825448402794460424567597321/2160500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-22680759544779916692103731289831722416800400088588711027/165062200000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-22680759544779916692103731289831722416800400088588711027/165062200000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(1920/4321), (-3871/4321), (-1007666793948327533107263/2700625000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(1920/4321), (-3871/4321), (-1007666793948327533107263/2700625000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-3871/4321), (-1920/4321), (-30316100594567369706326612659013697/16506220000000000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-3871/4321), (-1920/4321), (-30316100594567369706326612659013697/16506220000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004
