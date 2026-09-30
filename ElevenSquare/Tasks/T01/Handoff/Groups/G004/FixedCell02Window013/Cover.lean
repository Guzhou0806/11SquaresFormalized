import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window013.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window013.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window013.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window013
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(1408/4217), (-3975/4217), (42202343193394363950125101328147859269/183487954805950000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(1408/4217), (-3975/4217), (42202343193394363950125101328147859269/183487954805950000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(3975/4217), (1408/4217), (19120943481310013696132471556964506564633/7339518192238000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(3975/4217), (1408/4217), (19120943481310013696132471556964506564633/7339518192238000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window013
