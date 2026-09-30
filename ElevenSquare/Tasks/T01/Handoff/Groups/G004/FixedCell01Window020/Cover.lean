import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window020.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window020.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window020.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window020
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-6784/6905), (1287/6905), (-53877375384045345899089243033921/41277109490000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-6784/6905), (1287/6905), (-53877375384045345899089243033921/41277109490000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-1287/6905), (-6784/6905), (-13099931935087593360130345264044483664343/15767855825180000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-1287/6905), (-6784/6905), (-13099931935087593360130345264044483664343/15767855825180000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window020
