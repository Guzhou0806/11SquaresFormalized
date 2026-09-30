import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-61515624999873/4032500000000000), (-30515624999937/31503906250000), (-1487174275307054751596940387/806500000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-61515624999873/4032500000000000), (-30515624999937/31503906250000), (-1487174275307054751596940387/806500000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-30515624999937/31503906250000), (61515624999873/4032500000000000), (-21148446915360506578924929311069726810884017279/15404150000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-30515624999937/31503906250000), (61515624999873/4032500000000000), (-21148446915360506578924929311069726810884017279/15404150000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-61515624999873/4032500000000000), (-30515624999937/31503906250000), (-219011945305620358967878705313866890111883899/120344921875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(-61515624999873/4032500000000000), (-30515624999937/31503906250000), (-219011945305620358967878705313866890111883899/120344921875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025
