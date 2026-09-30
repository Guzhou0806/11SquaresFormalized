import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(1453124999997/31268000000000), (29546874999939/30535156250000), (10814651188596855368816237817/3908500000000000000000000000)⟩ :: nodeSource004 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource004, nodeSource006]
  change node006.Check (baselineFlip ⟨(1453124999997/31268000000000), (29546874999939/30535156250000), (10814651188596855368816237817/3908500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(1453124999997/31268000000000), (29546874999939/30535156250000), (328533501262077083529518145843157078518079053/116644296875000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(1453124999997/31268000000000), (29546874999939/30535156250000), (328533501262077083529518145843157078518079053/116644296875000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(29546874999939/30535156250000), (-1453124999997/31268000000000), (267151474852621082187175330544610969923017731/119443760000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(29546874999939/30535156250000), (-1453124999997/31268000000000), (267151474852621082187175330544610969923017731/119443760000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018
