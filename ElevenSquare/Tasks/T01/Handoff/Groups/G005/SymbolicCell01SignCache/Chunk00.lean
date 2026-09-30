import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk00
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial000 : Quartic := ⟨-1011627414051507787879335683986257459257, 1981373042052146003437001148457390000000, 7673993503232485739623520000000000000000, -11608596420774799076101558851542610000000, -4541609317903003551744184316013742540743⟩

theorem sign000 : polynomial000.BernsteinNonnegCheck (21/64) (31/64) := by
  norm_num [polynomial000, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry000 : CachedQuarticSign :=
  ⟨polynomial000, (21/64), (31/64),
    false, .leaf⟩

theorem entry000_checked : entry000.Check := by
  change polynomial000.BernsteinNonnegCheck (21/64) (31/64)
  exact sign000

def polynomial001 : Quartic := ⟨-101252594647032785071551472577, -591954233044703577088858000000, 7842489909294065570143102945154, 591954233044703577088858000000, -7741237314647032785071551472577⟩

theorem sign001 : polynomial001.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial001, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry001 : CachedQuarticSign :=
  ⟨polynomial001, (19/64), (5/16),
    false, .leaf⟩

theorem entry001_checked : entry001.Check := by
  change polynomial001.BernsteinNonnegCheck (19/64) (5/16)
  exact sign001

def polynomial002 : Quartic := ⟨-101393875413134224053937593267715741, 2700151567992261492807295646622891272, 1802721327599674430523286976870090102, -3347751052790701492807295646622891272, -2488841350508634224053937593267715741⟩

theorem sign002 : polynomial002.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial002, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry002 : CachedQuarticSign :=
  ⟨polynomial002, (1/2), (19/32),
    false, .leaf⟩

theorem entry002_checked : entry002.Check := by
  change polynomial002.BernsteinNonnegCheck (1/2) (19/32)
  exact sign002

def polynomial003 : Quartic := ⟨-1030488190276306476357358633257809935791736025141, 1750221157947135053886713683841549317678678335280, 5352382062247444604882658320000000000000000000000, -2929403996311990452288161356158450682321321664720, -260593708802825261974172326742190064208263974859⟩

theorem sign003 : polynomial003.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial003, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry003 : CachedQuarticSign :=
  ⟨polynomial003, (11/16), (27/32),
    false, .leaf⟩

theorem entry003_checked : entry003.Check := by
  change polynomial003.BernsteinNonnegCheck (11/16) (27/32)
  exact sign003

def polynomial004 : Quartic := ⟨-10378724385946206516554619162810578205719615, 639270752278790950247133081008343114373972296, -1085752441682707556132120000000000000000000000, -8538197022897156953336466918991656885626027704, -142931191352836575028445380837189421794280385⟩

theorem sign004 : polynomial004.BernsteinNonnegCheck (5/256) (11/64) := by
  norm_num [polynomial004, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry004 : CachedQuarticSign :=
  ⟨polynomial004, (5/256), (11/64),
    false, .leaf⟩

theorem entry004_checked : entry004.Check := by
  change polynomial004.BernsteinNonnegCheck (5/256) (11/64)
  exact sign004

def polynomial005 : Quartic := ⟨-10530231435471419624081675897082068433, 33098059556744956552927912016763400000, 219440775276875040000000000000000000000, -417090790887715797447072087983236600000, 241278295295307053624081675897082068433⟩

theorem sign005 : polynomial005.BernsteinNonnegCheck (61/128) (19/32) := by
  norm_num [polynomial005, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry005 : CachedQuarticSign :=
  ⟨polynomial005, (61/128), (19/32),
    false, .leaf⟩

theorem entry005_checked : entry005.Check := by
  change polynomial005.BernsteinNonnegCheck (61/128) (19/32)
  exact sign005

def polynomial006 : Quartic := ⟨-107434334820742131285955828535115230, 1104952966316206380304744599707713943, 2678375408299891589039305968490093262, 276321891128553619695255400292286057, -1465924847834282131285955828535115230⟩

theorem sign006 : polynomial006.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial006, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry006 : CachedQuarticSign :=
  ⟨polynomial006, (7/32), (1/4),
    false, .leaf⟩

theorem entry006_checked : entry006.Check := by
  change polynomial006.BernsteinNonnegCheck (7/32) (1/4)
  exact sign006

def polynomial007 : Quartic := ⟨-109064185428725683427835724815540873, 1315945052473341737781136973560283074, 2548064001015028540504590124718713500, 65329804971418262218863026439716926, -1467554698442265683427835724815540873⟩

theorem sign007 : polynomial007.BernsteinNonnegCheck (3/4) (27/32) := by
  norm_num [polynomial007, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry007 : CachedQuarticSign :=
  ⟨polynomial007, (3/4), (27/32),
    false, .leaf⟩

theorem entry007_checked : entry007.Check := by
  change polynomial007.BernsteinNonnegCheck (3/4) (27/32)
  exact sign007

def polynomial008 : Quartic := ⟨-1129289201348518235861843105354702847253966649, 101569303772049877377153592890261101230000000, 8299220959281620066528840000000000000000000000, -2623365275543137852130606407109738898770000000, -540870140828493699384276894645297152746033351⟩

theorem sign008 : polynomial008.BernsteinNonnegCheck (117/128) 1 := by
  norm_num [polynomial008, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry008 : CachedQuarticSign :=
  ⟨polynomial008, (117/128), 1,
    false, .leaf⟩

theorem entry008_checked : entry008.Check := by
  change polynomial008.BernsteinNonnegCheck (117/128) 1
  exact sign008

def polynomial009 : Quartic := ⟨-112997267, 170477230, 112997267, 0, 0⟩

theorem sign009 : polynomial009.BernsteinNonnegCheck (1/2) 1 := by
  norm_num [polynomial009, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry009 : CachedQuarticSign :=
  ⟨polynomial009, (1/2), 1,
    false, .leaf⟩

theorem entry009_checked : entry009.Check := by
  change polynomial009.BernsteinNonnegCheck (1/2) 1
  exact sign009

def polynomial010 : Quartic := ⟨-1178505993, 59202880, 1178505993, 0, 0⟩

theorem sign010 : polynomial010.BernsteinNonnegCheck (125/128) 1 := by
  norm_num [polynomial010, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry010 : CachedQuarticSign :=
  ⟨polynomial010, (125/128), 1,
    false, .leaf⟩

theorem entry010_checked : entry010.Check := by
  change polynomial010.BernsteinNonnegCheck (125/128) 1
  exact sign010

def polynomial011 : Quartic := ⟨-12024611703997272909022076763318561748843, 40484820554850712562555471789129610000000, -2700616009187945538467200000000000000000, -24732221210337478852263568210870390000000, -6248658613758231952510723236681438251157⟩

theorem sign011 : polynomial011.BernsteinNonnegCheck (21/64) (19/32) := by
  norm_num [polynomial011, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry011 : CachedQuarticSign :=
  ⟨polynomial011, (21/64), (19/32),
    false, .leaf⟩

theorem entry011_checked : entry011.Check := by
  change polynomial011.BernsteinNonnegCheck (21/64) (19/32)
  exact sign011

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk00
