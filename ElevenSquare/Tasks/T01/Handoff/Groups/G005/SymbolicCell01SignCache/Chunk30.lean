import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk30
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial360 : Quartic := ⟨97432636359131138593245516841001520841387613, 210957352954731492308454870165860558910958822, -1205114287511816785575448000000000000000000000, -347921480065771810881817129834139441089041178, 125284865825884079585834483158998479158612387⟩

theorem sign360 : polynomial360.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial360, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry360 : CachedQuarticSign :=
  ⟨polynomial360, (19/64), (5/16),
    false, .leaf⟩

theorem entry360_checked : entry360.Check := by
  change polynomial360.BernsteinNonnegCheck (19/64) (5/16)
  exact sign360

def polynomial361 : Quartic := ⟨987107495, -2804649182, -987107495, 0, 0⟩

theorem sign361 : polynomial361.BernsteinNonnegCheck 0 (5/16) := by
  norm_num [polynomial361, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry361 : CachedQuarticSign :=
  ⟨polynomial361, 0, (5/16),
    false, .leaf⟩

theorem entry361_checked : entry361.Check := by
  change polynomial361.BernsteinNonnegCheck 0 (5/16)
  exact sign361

def polynomial362 : Quartic := ⟨98750743997067783095034034008852574354203761, -106354693157218946216120000000000000000000000, -786063548200508397227805965991147425645796239, 0, 0⟩

theorem sign362 : polynomial362.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial362, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry362 : CachedQuarticSign :=
  ⟨polynomial362, (7/32), (1/4),
    false, .leaf⟩

theorem entry362_checked : entry362.Check := by
  change polynomial362.BernsteinNonnegCheck (7/32) (1/4)
  exact sign362

def polynomial363 : Quartic := ⟨9932145106241624586427993845, -938817199280656983595697446042, 7620120429787516750827144012310, 938817199280656983595697446042, -7630052574893758375413572006155⟩

theorem sign363 : polynomial363.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial363, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry363 : CachedQuarticSign :=
  ⟨polynomial363, (7/32), (1/4),
    false, .leaf⟩

theorem entry363_checked : entry363.Check := by
  change polynomial363.BernsteinNonnegCheck (7/32) (1/4)
  exact sign363

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk30
