import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk07
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial084 : Quartic := ⟨-487928903061598278737, 194461691949808809918, 10975837806123196557474, -194461691949808809918, -10487908903061598278737⟩

theorem sign084 : polynomial084.BernsteinNonnegCheck (21/64) (61/128) := by
  norm_num [polynomial084, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry084 : CachedQuarticSign :=
  ⟨polynomial084, (21/64), (61/128),
    false, .leaf⟩

theorem entry084_checked : entry084.Check := by
  change polynomial084.BernsteinNonnegCheck (21/64) (61/128)
  exact sign084

def polynomial085 : Quartic := ⟨-502299065863323465744358859330762309003221351, 2389617253855974580000000000000000000000000000, -865176101574244632937718859330762309003221351, 0, 0⟩

theorem sign085 : polynomial085.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial085, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry085 : CachedQuarticSign :=
  ⟨polynomial085, (27/32), 1,
    false, .leaf⟩

theorem entry085_checked : entry085.Check := by
  change polynomial085.BernsteinNonnegCheck (27/32) 1
  exact sign085

def polynomial086 : Quartic := ⟨-509333333, 509333334, 509333333, 0, 0⟩

theorem sign086 : polynomial086.BernsteinNonnegCheck (11/16) 1 := by
  norm_num [polynomial086, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry086 : CachedQuarticSign :=
  ⟨polynomial086, (11/16), 1,
    false, .leaf⟩

theorem entry086_checked : entry086.Check := by
  change polynomial086.BernsteinNonnegCheck (11/16) 1
  exact sign086

def polynomial087 : Quartic := ⟨-540223, 1419504, 540223, 0, 0⟩

theorem sign087 : polynomial087.BernsteinNonnegCheck (91/256) (23/32) := by
  norm_num [polynomial087, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry087 : CachedQuarticSign :=
  ⟨polynomial087, (91/256), (23/32),
    false, .leaf⟩

theorem entry087_checked : entry087.Check := by
  change polynomial087.BernsteinNonnegCheck (91/256) (23/32)
  exact sign087

def polynomial088 : Quartic := ⟨-540223, 1419504, 540223, 0, 0⟩

theorem sign088 : polynomial088.BernsteinPosCheck (3/4) 1 := by
  norm_num [polynomial088, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry088 : CachedQuarticSign :=
  ⟨polynomial088, (3/4), 1,
    true, .leaf⟩

theorem entry088_checked : entry088.Check := by
  change polynomial088.BernsteinPosCheck (3/4) 1
  exact sign088

def polynomial089 : Quartic := ⟨-5615230191119027681251032484769130211319, 103602376720927553703200000000000000000000, -73846922407260273978051032484769130211319, 0, 0⟩

theorem sign089 : polynomial089.BernsteinNonnegCheck (7/32) 1 := by
  norm_num [polynomial089, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry089 : CachedQuarticSign :=
  ⟨polynomial089, (7/32), 1,
    false, .leaf⟩

theorem entry089_checked : entry089.Check := by
  change polynomial089.BernsteinNonnegCheck (7/32) 1
  exact sign089

def polynomial090 : Quartic := ⟨-56455533976134632648504639954477619258555209, 338862086421754542298280000000000000000000000, -197689204339411907146584639954477619258555209, 0, 0⟩

theorem sign090 : polynomial090.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial090, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry090 : CachedQuarticSign :=
  ⟨polynomial090, (21/64), (91/256),
    false, .leaf⟩

theorem entry090_checked : entry090.Check := by
  change polynomial090.BernsteinNonnegCheck (21/64) (91/256)
  exact sign090

def polynomial091 : Quartic := ⟨-57025233827822442181734886155874883370355823, 3049108106968512376967907000000000000000000000, -3106133340796334819149641886155874883370355823, 0, 0⟩

theorem sign091 : polynomial091.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial091, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry091 : CachedQuarticSign :=
  ⟨polynomial091, (11/16), (27/32),
    false, .leaf⟩

theorem entry091_checked : entry091.Check := by
  change polynomial091.BernsteinNonnegCheck (11/16) (27/32)
  exact sign091

def polynomial092 : Quartic := ⟨-57301, 984719, 57301, 0, 0⟩

theorem sign092 : polynomial092.BernsteinPosCheck (5/32) (1/4) := by
  norm_num [polynomial092, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry092 : CachedQuarticSign :=
  ⟨polynomial092, (5/32), (1/4),
    true, .leaf⟩

theorem entry092_checked : entry092.Check := by
  change polynomial092.BernsteinPosCheck (5/32) (1/4)
  exact sign092

def polynomial093 : Quartic := ⟨-590440844736540528191430303862540992051469039947855121, 1255797616724068773865813746682440000000000000000000000, 526256171122901376709817071959579007948530960052144879, 0, 0⟩

theorem sign093 : polynomial093.BernsteinNonnegCheck (61/128) (19/32) := by
  norm_num [polynomial093, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry093 : CachedQuarticSign :=
  ⟨polynomial093, (61/128), (19/32),
    false, .leaf⟩

theorem entry093_checked : entry093.Check := by
  change polynomial093.BernsteinNonnegCheck (61/128) (19/32)
  exact sign093

def polynomial094 : Quartic := ⟨-6188744061457255100349450417731, 31269222529394427370227745953419, -40876867705553117716210229164538, 6930701070605572629772254046581, 7817894585209424899650549582269⟩

theorem sign094 : polynomial094.BernsteinNonnegCheck (21/64) (31/64) := by
  norm_num [polynomial094, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry094 : CachedQuarticSign :=
  ⟨polynomial094, (21/64), (31/64),
    false, .leaf⟩

theorem entry094_checked : entry094.Check := by
  change polynomial094.BernsteinNonnegCheck (21/64) (31/64)
  exact sign094

def polynomial095 : Quartic := ⟨-62014344564598280775326953723339, 444406817344566856370710161600000, -506060019288000000000000000000000, 270863617344566856370710161600000, 568073525276598280775326953723339⟩

theorem sign095 : polynomial095.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial095, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry095 : CachedQuarticSign :=
  ⟨polynomial095, (21/64), (91/256),
    false, .leaf⟩

theorem entry095_checked : entry095.Check := by
  change polynomial095.BernsteinNonnegCheck (21/64) (91/256)
  exact sign095

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk07
