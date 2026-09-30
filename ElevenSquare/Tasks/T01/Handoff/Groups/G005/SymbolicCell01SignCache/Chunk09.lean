import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk09
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial108 : Quartic := ⟨-78429512675231929233745433702142134947581305, -264934502401634402598785194999337021463241502, 569450643550766893836395000000000000000000000, 380631007358890959146914805000662978536758498, -104260480217306461756379566297857865052418695⟩

theorem sign108 : polynomial108.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial108, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry108 : CachedQuarticSign :=
  ⟨polynomial108, (11/16), (27/32),
    false, .leaf⟩

theorem entry108_checked : entry108.Check := by
  change polynomial108.BernsteinNonnegCheck (11/16) (27/32)
  exact sign108

def polynomial109 : Quartic := ⟨-84621420347215914797462591153438187487753685, 1857532137623824189028464652868044474359629166, 2449253484062674281121120000000000000000000000, -2445478808051834661446975347131955525640370834, 2223617018685339919044102591153438187487753685⟩

theorem sign109 : polynomial109.BernsteinNonnegCheck (1/16) (11/64) := by
  norm_num [polynomial109, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry109 : CachedQuarticSign :=
  ⟨polynomial109, (1/16), (11/64),
    false, .leaf⟩

theorem entry109_checked : entry109.Check := by
  change polynomial109.BernsteinNonnegCheck (1/16) (11/64)
  exact sign109

def polynomial110 : Quartic := ⟨-84888889, 382000000, 84888889, 0, 0⟩

theorem sign110 : polynomial110.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial110, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry110 : CachedQuarticSign :=
  ⟨polynomial110, (27/32), 1,
    false, .leaf⟩

theorem entry110_checked : entry110.Check := by
  change polynomial110.BernsteinNonnegCheck (27/32) 1
  exact sign110

def polynomial111 : Quartic := ⟨-86159333523779997658332400457, 360978083014637453014468464934, 7639984720000000000000000000000, 360978083014637453014468464934, 7726144053523779997658332400457⟩

theorem sign111 : polynomial111.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial111, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry111 : CachedQuarticSign :=
  ⟨polynomial111, (101/256), (19/32),
    false, .leaf⟩

theorem entry111_checked : entry111.Check := by
  change polynomial111.BernsteinNonnegCheck (101/256) (19/32)
  exact sign111

def polynomial112 : Quartic := ⟨-89938757172432767478800724091000000, 75340338214125336772156052632748797, 1563321683480000000000000000000000, -130539707785874663227843947367251203, 294255072855912767478800724091000000⟩

theorem sign112 : polynomial112.BernsteinNonnegCheck (115/128) 1 := by
  norm_num [polynomial112, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry112 : CachedQuarticSign :=
  ⟨polynomial112, (115/128), 1,
    false, .leaf⟩

theorem entry112_checked : entry112.Check := by
  change polynomial112.BernsteinNonnegCheck (115/128) 1
  exact sign112

def polynomial113 : Quartic := ⟨-9034379585704601986232718766129622140000, 260307749138884885884230729150904284240857, -34555561803616970242400000000000000000000, -77065011752743437116569270849095715759143, 144883430887058601986232718766129622140000⟩

theorem sign113 : polynomial113.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial113, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry113 : CachedQuarticSign :=
  ⟨polynomial113, (21/64), (91/256),
    false, .leaf⟩

theorem entry113_checked : entry113.Check := by
  change polynomial113.BernsteinNonnegCheck (21/64) (91/256)
  exact sign113

def polynomial114 : Quartic := ⟨-93253, 520839, 93253, 0, 0⟩

theorem sign114 : polynomial114.BernsteinNonnegCheck (7/32) (23/32) := by
  norm_num [polynomial114, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry114 : CachedQuarticSign :=
  ⟨polynomial114, (7/32), (23/32),
    false, .leaf⟩

theorem entry114_checked : entry114.Check := by
  change polynomial114.BernsteinNonnegCheck (7/32) (23/32)
  exact sign114

def polynomial115 : Quartic := ⟨-93253, 520839, 93253, 0, 0⟩

theorem sign115 : polynomial115.BernsteinPosCheck (19/64) (27/32) := by
  norm_num [polynomial115, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry115 : CachedQuarticSign :=
  ⟨polynomial115, (19/64), (27/32),
    true, .leaf⟩

theorem entry115_checked : entry115.Check := by
  change polynomial115.BernsteinPosCheck (19/64) (27/32)
  exact sign115

def polynomial116 : Quartic := ⟨-93508142087475851217050426356556447059, 863297393281760240000000000000000000000, -744729858241438651217050426356556447059, 0, 0⟩

theorem sign116 : polynomial116.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial116, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry116 : CachedQuarticSign :=
  ⟨polynomial116, (11/16), (27/32),
    false, .leaf⟩

theorem entry116_checked : entry116.Check := by
  change polynomial116.BernsteinNonnegCheck (11/16) (27/32)
  exact sign116

def polynomial117 : Quartic := ⟨-9603964823412783711226210631, 664610893146407066773025976424, 1110349489544600000000000000000, -8375168246161432933226974023576, 7939026795497452783711226210631⟩

theorem sign117 : polynomial117.BernsteinNonnegCheck (61/128) (31/64) := by
  norm_num [polynomial117, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry117 : CachedQuarticSign :=
  ⟨polynomial117, (61/128), (31/64),
    false, .leaf⟩

theorem entry117_checked : entry117.Check := by
  change polynomial117.BernsteinNonnegCheck (61/128) (31/64)
  exact sign117

def polynomial118 : Quartic := ⟨-976037866901967088657705053640528135035921, 27055056777882019498974626906261407871388375, -18931513612834434125228000000000000000000000, -29479395341071270333693373093738592128611625, 3293375238071675381217705053640528135035921⟩

theorem sign118 : polynomial118.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial118, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry118 : CachedQuarticSign :=
  ⟨polynomial118, (19/64), (5/16),
    false, .leaf⟩

theorem entry118_checked : entry118.Check := by
  change polynomial118.BernsteinNonnegCheck (19/64) (5/16)
  exact sign118

def polynomial119 : Quartic := ⟨-98177248526047267837097943362299718254392587, 179489100528226776555418507258640944683214826, 90718823489641727196835000000000000000000000, -155165278887084592626941492741359055316785174, -73853426932661278167727056637700281745607413⟩

theorem sign119 : polynomial119.BernsteinNonnegCheck (11/16) (23/32) := by
  norm_num [polynomial119, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry119 : CachedQuarticSign :=
  ⟨polynomial119, (11/16), (23/32),
    false, .leaf⟩

theorem entry119_checked : entry119.Check := by
  change polynomial119.BernsteinNonnegCheck (11/16) (23/32)
  exact sign119

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk09
