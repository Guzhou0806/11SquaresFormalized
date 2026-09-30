import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window012.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window012.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window012.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window012.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window012
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-20001084479000410693494371953/47750000000000000000000000000), (18449633035867035385990508739/152800000000000000000000000000), (-462880162223646648187856158301979762010921641767235660502381/927739309246400000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(-20001084479000410693494371953/47750000000000000000000000000), (18449633035867035385990508739/152800000000000000000000000000), (-462880162223646648187856158301979762010921641767235660502381/927739309246400000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-5248/5777), (2415/5777), (-27927621062639647725883688671657107221/28991853413950000000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(-5248/5777), (2415/5777), (-27927621062639647725883688671657107221/28991853413950000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-2415/5777), (-5248/5777), (-2735727544367873455085179041981617136263/2319348273116000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(-2415/5777), (-5248/5777), (-2735727544367873455085179041981617136263/2319348273116000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window012
