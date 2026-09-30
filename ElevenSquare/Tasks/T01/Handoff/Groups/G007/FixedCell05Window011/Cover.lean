import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node008_checked : node008.Check nodeSource008 targets := by
  refine ⟨node009_checked, ?_⟩
  have he : baselineFlip ⟨(-4812499999989/5890625000000), (11812499999973/37700000000000), (-115061455374151939887715623/188500000000000000000000000)⟩ :: nodeSource008 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource008, nodeSource010]
  change node010.Check (baselineFlip ⟨(-4812499999989/5890625000000), (11812499999973/37700000000000), (-115061455374151939887715623/188500000000000000000000000)⟩ :: nodeSource008) targets
  rw [he]
  exact node010_checked

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-927150637095733497735916422760443300967744645473277649/3600350000000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-927150637095733497735916422760443300967744645473277649/3600350000000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-1748137436793342259894105121374820429973521959943981499/14401400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-1748137436793342259894105121374820429973521959943981499/14401400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-352/377), (135/377), (-140782620312670636752799/235625000000000000000000)⟩ :: nodeSource001 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource001, nodeSource007]
  change node007.Check (baselineFlip ⟨(-352/377), (135/377), (-140782620312670636752799/235625000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node007_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-135/377), (-352/377), (-50182140409609024577398795368597/27695000000000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-135/377), (-352/377), (-50182140409609024577398795368597/27695000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011
