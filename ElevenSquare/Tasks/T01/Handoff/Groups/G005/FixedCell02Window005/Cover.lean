import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window005.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window005.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window005.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window005.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(387708359002281417731/5000000000000000000000), (-320893285263457706409451472577/3820000000000000000000000000000), (589995579513415141926561252836742887325971578757609579371301377/4031006018141680000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(387708359002281417731/5000000000000000000000), (-320893285263457706409451472577/3820000000000000000000000000000), (589995579513415141926561252836742887325971578757609579371301377/4031006018141680000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(7936/17345), (-15423/17345), (3187058323139773443800399124975547/5276185887620000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(7936/17345), (-15423/17345), (3187058323139773443800399124975547/5276185887620000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(15423/17345), (7936/17345), (13708927984419406775142193973359142905657429/5038757522677100000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(15423/17345), (7936/17345), (13708927984419406775142193973359142905657429/5038757522677100000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window005
