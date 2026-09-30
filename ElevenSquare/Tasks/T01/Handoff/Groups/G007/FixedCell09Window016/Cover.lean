import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.CoverLeaf008
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node007_checked : node007.Check nodeSource007 targets := by
  refine ⟨node008_checked, ?_⟩
  have he : baselineFlip ⟨(-4992/5617), (2575/5617), (-989849318745341382635409/3510625000000000000000000)⟩ :: nodeSource007 = nodeSource009 := by
    norm_num [baselineFlip, nodeSource007, nodeSource009]
  change node009.Check (baselineFlip ⟨(-4992/5617), (2575/5617), (-989849318745341382635409/3510625000000000000000000)⟩ :: nodeSource007) targets
  rw [he]
  exact node009_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(49890624999897/112340000000000), (18890624999961/21941406250000), (6574512970339831077557173617/2808500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(49890624999897/112340000000000), (18890624999961/21941406250000), (6574512970339831077557173617/2808500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(18890624999961/21941406250000), (-49890624999897/112340000000000), (1655256331002455712231955617/2808500000000000000000000000)⟩ :: nodeSource004 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource004, nodeSource010]
  change node010.Check (baselineFlip ⟨(18890624999961/21941406250000), (-49890624999897/112340000000000), (1655256331002455712231955617/2808500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node010_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-18890624999961/21941406250000), (49890624999897/112340000000000), (-70292111340065857514962129208314582456675431/429138800000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-18890624999961/21941406250000), (49890624999897/112340000000000), (-70292111340065857514962129208314582456675431/429138800000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-49890624999897/112340000000000), (-18890624999961/21941406250000), (-201162344507705049175445081142861132148725747/83816171875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-49890624999897/112340000000000), (-18890624999961/21941406250000), (-201162344507705049175445081142861132148725747/83816171875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016
