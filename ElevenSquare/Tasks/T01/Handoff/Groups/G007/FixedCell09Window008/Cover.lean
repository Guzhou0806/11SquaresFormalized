import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(-3712/4937), (3255/4937), (1052999788468315840204391/3085625000000000000000000)⟩ :: nodeSource004 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource004, nodeSource006]
  change node006.Check (baselineFlip ⟨(-3712/4937), (3255/4937), (1052999788468315840204391/3085625000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-14046874999971/19285156250000), (315328124999349/493700000000000), (1031908054222643243915323417821818046820352373/1885934000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-14046874999971/19285156250000), (315328124999349/493700000000000), (1031908054222643243915323417821818046820352373/1885934000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-315328124999349/493700000000000), (-14046874999971/19285156250000), (-181816635068720526630286760574031220867201517/73669296875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-315328124999349/493700000000000), (-14046874999971/19285156250000), (-181816635068720526630286760574031220867201517/73669296875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008
