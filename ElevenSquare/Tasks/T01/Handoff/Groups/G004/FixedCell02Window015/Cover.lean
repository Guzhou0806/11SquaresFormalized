import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node006_checked : node006.Check nodeSource006 targets := by
  refine ⟨node007_checked, ?_⟩
  have he : baselineFlip ⟨(-2388499999994703/4651428125000000), (551743499998776393/744228500000000000), (-1314934052588758794331153505489271/3942178364500000000000000000000000)⟩ :: nodeSource006 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource006, nodeSource008]
  change node008.Check (baselineFlip ⟨(-2388499999994703/4651428125000000), (551743499998776393/744228500000000000), (-1314934052588758794331153505489271/3942178364500000000000000000000000)⟩ :: nodeSource006) targets
  rw [he]
  exact node008_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (3878822919432141032488757926879592475046980932468579930538159873553/4344031985360000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (3878822919432141032488757926879592475046980932468579930538159873553/4344031985360000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(160/281), (-231/281), (56933126525878200338854444927104679/71073821750000000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(160/281), (-231/281), (56933126525878200338854444927104679/71073821750000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(231/281), (160/281), (571980264506094285888967715641739419/227436229600000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(231/281), (160/281), (571980264506094285888967715641739419/227436229600000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015
