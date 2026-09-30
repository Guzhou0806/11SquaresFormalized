import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CoverLeaf008
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CoverLeaf011
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CoverLeaf012

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node010_checked : node010.Check nodeSource010 targets := by
  refine ⟨node011_checked, ?_⟩
  have he : baselineFlip ⟨(479531249998977/512500000000000), (468749999999/8007812500000), (30104300312616558742666281/20500000000000000000000000)⟩ :: nodeSource010 = nodeSource012 := by
    norm_num [baselineFlip, nodeSource010, nodeSource012]
  change node012.Check (baselineFlip ⟨(479531249998977/512500000000000), (468749999999/8007812500000), (30104300312616558742666281/20500000000000000000000000)⟩ :: nodeSource010) targets
  rw [he]
  exact node012_checked

theorem node007_checked : node007.Check nodeSource007 targets := by
  refine ⟨node008_checked, ?_⟩
  have he : baselineFlip ⟨(468749999999/8007812500000), (-479531249998977/512500000000000), (-36377316541422863808044799/20500000000000000000000000)⟩ :: nodeSource007 = nodeSource009 := by
    norm_num [baselineFlip, nodeSource007, nodeSource009]
  change node009.Check (baselineFlip ⟨(468749999999/8007812500000), (-479531249998977/512500000000000), (-36377316541422863808044799/20500000000000000000000000)⟩ :: nodeSource007) targets
  rw [he]
  exact node009_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(479531249998977/512500000000000), (468749999999/8007812500000), (30965606303202221289886361/20500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(479531249998977/512500000000000), (468749999999/8007812500000), (30965606303202221289886361/20500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(468749999999/8007812500000), (-479531249998977/512500000000000), (-35302224358425157338035199/20500000000000000000000000)⟩ :: nodeSource004 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource004, nodeSource010]
  change node010.Check (baselineFlip ⟨(468749999999/8007812500000), (-479531249998977/512500000000000), (-35302224358425157338035199/20500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node010_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(468749999999/8007812500000), (-479531249998977/512500000000000), (-3190587392377183539954743193981220295965553729/1957750000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(468749999999/8007812500000), (-479531249998977/512500000000000), (-3190587392377183539954743193981220295965553729/1957750000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-479531249998977/512500000000000), (-468749999999/8007812500000), (-46219194829336543918130690932652946757839923/30589843750000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-479531249998977/512500000000000), (-468749999999/8007812500000), (-46219194829336543918130690932652946757839923/30589843750000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000
