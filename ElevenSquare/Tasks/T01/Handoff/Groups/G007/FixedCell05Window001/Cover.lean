import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node006_checked : node006.Check nodeSource006 targets := by
  refine ⟨node007_checked, ?_⟩
  have he : baselineFlip ⟨(1152/4177), (-4015/4177), (-12617631019379215303772379170238897/15956140000000000000000000000000000)⟩ :: nodeSource006 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource006, nodeSource008]
  change node008.Check (baselineFlip ⟨(1152/4177), (-4015/4177), (-12617631019379215303772379170238897/15956140000000000000000000000000000)⟩ :: nodeSource006) targets
  rw [he]
  exact node008_checked

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-4015/4177), (-1152/4177), (-26829764000539252038430004149652913/15956140000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-4015/4177), (-1152/4177), (-26829764000539252038430004149652913/15956140000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-4359374999991/16316406250000), (388953124999197/417700000000000), (1909644235907096774299248177/2088500000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-4359374999991/16316406250000), (388953124999197/417700000000000), (1909644235907096774299248177/2088500000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(388953124999197/417700000000000), (4359374999991/16316406250000), (4555695828104837083108893177/2088500000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(388953124999197/417700000000000), (4359374999991/16316406250000), (4555695828104837083108893177/2088500000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001
