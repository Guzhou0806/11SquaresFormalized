import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-1016573087497934593793/65580712832500000000000), (-504284287498975428417/512349319003906250000), (-115265190511171571080760946145716365907747/213308364320834726500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-1016573087497934593793/65580712832500000000000), (-504284287498975428417/512349319003906250000), (-115265190511171571080760946145716365907747/213308364320834726500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (73801424361196482517562196804264096523049486625378743627287360226181557/76558399514957840000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (73801424361196482517562196804264096523049486625378743627287360226181557/76558399514957840000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(8064/8065), (-127/8065), (1218052583658875308123945597103314550314551/501036646040300000000000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(8064/8065), (-127/8065), (1218052583658875308123945597103314550314551/501036646040300000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-127/8065), (-8064/8065), (-266784134631485156327147737804750236090343/501036646040300000000000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-127/8065), (-8064/8065), (-266784134631485156327147737804750236090343/501036646040300000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022
