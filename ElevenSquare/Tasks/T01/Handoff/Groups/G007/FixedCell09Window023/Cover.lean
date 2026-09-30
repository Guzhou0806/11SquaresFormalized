import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-28578124999941/29597656250000), (59578124999877/757700000000000), (-3528597896308508139256441614136174056994126971/2894414000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-28578124999941/29597656250000), (59578124999877/757700000000000), (-3528597896308508139256441614136174056994126971/2894414000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-59578124999877/757700000000000), (-28578124999941/29597656250000), (-218838982609462664621683527284795933305524207/113063046875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-59578124999877/757700000000000), (-28578124999941/29597656250000), (-218838982609462664621683527284795933305524207/113063046875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023
