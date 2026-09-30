import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(10171874999979/17722656250000), (-354078124999269/453700000000000), (-1153494563649597451243589463/2268500000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(10171874999979/17722656250000), (-354078124999269/453700000000000), (-1153494563649597451243589463/2268500000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(354078124999269/453700000000000), (10171874999979/17722656250000), (224831896641599943047940983122180786704482133/67700546875000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(354078124999269/453700000000000), (10171874999979/17722656250000), (224831896641599943047940983122180786704482133/67700546875000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(10171874999979/17722656250000), (-354078124999269/453700000000000), (-413601276032926054069096654688254199742546213/1733134000000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(10171874999979/17722656250000), (-354078124999269/453700000000000), (-413601276032926054069096654688254199742546213/1733134000000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004
