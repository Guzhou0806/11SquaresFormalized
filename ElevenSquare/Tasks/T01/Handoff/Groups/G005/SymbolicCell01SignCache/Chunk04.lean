import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk04
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial048 : Quartic := ⟨-236521989232305071948736803267, 674061389210664000000000000000, -436178887253849071948736803267, 0, 0⟩

theorem sign048 : polynomial048.BernsteinNonnegCheck (11/16) 1 := by
  norm_num [polynomial048, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry048 : CachedQuarticSign :=
  ⟨polynomial048, (11/16), 1,
    false, .leaf⟩

theorem entry048_checked : entry048.Check := by
  change polynomial048.BernsteinNonnegCheck (11/16) 1
  exact sign048

def polynomial049 : Quartic := ⟨-241542985116017388316319874222323055061161113, 1085077410264289642904768000000000000000000000, -362599347966232679271631874222323055061161113, 0, 0⟩

theorem sign049 : polynomial049.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial049, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry049 : CachedQuarticSign :=
  ⟨polynomial049, (27/32), 1,
    false, .leaf⟩

theorem entry049_checked : entry049.Check := by
  change polynomial049.BernsteinNonnegCheck (27/32) 1
  exact sign049

def polynomial050 : Quartic := ⟨-242412477837069742880266050160789003291574801, 14821870032705095571777111000000000000000000000, -15064282510542165314657377050160789003291574801, 0, 0⟩

theorem sign050 : polynomial050.BernsteinNonnegCheck (21/64) (27/32) := by
  norm_num [polynomial050, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry050 : CachedQuarticSign :=
  ⟨polynomial050, (21/64), (27/32),
    false, .leaf⟩

theorem entry050_checked : entry050.Check := by
  change polynomial050.BernsteinNonnegCheck (21/64) (27/32)
  exact sign050

def polynomial051 : Quartic := ⟨-261103240593691317809691750000, 489228759966764166121477408823, 47582372948195562078598515130, 465770285033235833878522591177, -738602763093691317809691750000⟩

theorem sign051 : polynomial051.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial051, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry051 : CachedQuarticSign :=
  ⟨polynomial051, (1/2), (19/32),
    false, .leaf⟩

theorem entry051_checked : entry051.Check := by
  change polynomial051.BernsteinNonnegCheck (1/2) (19/32)
  exact sign051

def polynomial052 : Quartic := ⟨-264795949025095595041, 245832819954371645380, 7999992000000000000000, -15754167180045628354620, 8264787949025095595041⟩

theorem sign052 : polynomial052.BernsteinNonnegCheck (11/16) 1 := by
  norm_num [polynomial052, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry052 : CachedQuarticSign :=
  ⟨polynomial052, (11/16), 1,
    false, .leaf⟩

theorem entry052_checked : entry052.Check := by
  change polynomial052.BernsteinNonnegCheck (11/16) 1
  exact sign052

def polynomial053 : Quartic := ⟨-268211, 174831, 268211, 0, 0⟩

theorem sign053 : polynomial053.BernsteinNonnegCheck (3/4) 1 := by
  norm_num [polynomial053, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry053 : CachedQuarticSign :=
  ⟨polynomial053, (3/4), 1,
    false, .leaf⟩

theorem entry053_checked : entry053.Check := by
  change polynomial053.BernsteinNonnegCheck (3/4) 1
  exact sign053

def polynomial054 : Quartic := ⟨-268211, 174831, 268211, 0, 0⟩

theorem sign054 : polynomial054.BernsteinPosCheck (27/32) 1 := by
  norm_num [polynomial054, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry054 : CachedQuarticSign :=
  ⟨polynomial054, (27/32), 1,
    true, .leaf⟩

theorem entry054_checked : entry054.Check := by
  change polynomial054.BernsteinPosCheck (27/32) 1
  exact sign054

def polynomial055 : Quartic := ⟨-28035686530185105870508940859, 110355445244444400000000000000, -104435644085740705870508940859, 0, 0⟩

theorem sign055 : polynomial055.BernsteinNonnegCheck (61/128) (19/32) := by
  norm_num [polynomial055, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry055 : CachedQuarticSign :=
  ⟨polynomial055, (61/128), (19/32),
    false, .leaf⟩

theorem entry055_checked : entry055.Check := by
  change polynomial055.BernsteinNonnegCheck (61/128) (19/32)
  exact sign055

def polynomial056 : Quartic := ⟨-287002440119564107429431863803061978306070348, 727271454596040484145108882231185619960778649, 344061349603329215190660000000000000000000000, -611346063065204992584331117768814380039221351, -419934206070507770186548136196938021693929652⟩

theorem sign056 : polynomial056.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial056, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry056 : CachedQuarticSign :=
  ⟨polynomial056, (101/256), (19/32),
    false, .leaf⟩

theorem entry056_checked : entry056.Check := by
  change polynomial056.BernsteinNonnegCheck (101/256) (19/32)
  exact sign056

def polynomial057 : Quartic := ⟨-314777826430958083838511792310027785, 3362849056547383379533008524372886576, -1989605692452920000000000000000000000, 4640001116547383379533008524372886576, 1027230033978038083838511792310027785⟩

theorem sign057 : polynomial057.BernsteinNonnegCheck (7/64) (11/64) := by
  norm_num [polynomial057, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry057 : CachedQuarticSign :=
  ⟨polynomial057, (7/64), (11/64),
    false, .leaf⟩

theorem entry057_checked : entry057.Check := by
  change polynomial057.BernsteinNonnegCheck (7/64) (11/64)
  exact sign057

def polynomial058 : Quartic := ⟨-320498510100182453250606736196888700782227315, 1204185315058686399916145122284451013657886376, 7545437871091365345421320000000000000000000000, -4885706703337984509949214877715548986342113624, -382278393275315502517753263803111299217772685⟩

theorem sign058 : polynomial058.BernsteinNonnegCheck (5/32) (1/4) := by
  norm_num [polynomial058, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry058 : CachedQuarticSign :=
  ⟨polynomial058, (5/32), (1/4),
    false, .leaf⟩

theorem entry058_checked : entry058.Check := by
  change polynomial058.BernsteinNonnegCheck (5/32) (1/4)
  exact sign058

def polynomial059 : Quartic := ⟨-32107495, 1913315848, 32107495, 0, 0⟩

theorem sign059 : polynomial059.BernsteinNonnegCheck (5/256) (5/16) := by
  norm_num [polynomial059, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry059 : CachedQuarticSign :=
  ⟨polynomial059, (5/256), (5/16),
    false, .leaf⟩

theorem entry059_checked : entry059.Check := by
  change polynomial059.BernsteinNonnegCheck (5/256) (5/16)
  exact sign059

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk04
