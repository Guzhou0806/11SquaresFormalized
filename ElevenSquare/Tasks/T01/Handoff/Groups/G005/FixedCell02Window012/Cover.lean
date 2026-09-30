import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window012.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window012.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window012.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window012.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window012
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(387708359002281417731/5000000000000000000000), (-320893285263457706409451472577/3820000000000000000000000000000), (124166471647336530807124304999384011153533950381615407551760778341/859142488312811440000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(387708359002281417731/5000000000000000000000), (-320893285263457706409451472577/3820000000000000000000000000000), (124166471647336530807124304999384011153533950381615407551760778341/859142488312811440000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(144384/282025), (-242263/282025), (4167991957905894156939470007423062499/5622660263827300000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(144384/282025), (-242263/282025), (4167991957905894156939470007423062499/5622660263827300000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(242263/282025), (144384/282025), (14606089519802907611657599899298176396611357357/5369640551955071500000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(242263/282025), (144384/282025), (14606089519802907611657599899298176396611357357/5369640551955071500000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window012
