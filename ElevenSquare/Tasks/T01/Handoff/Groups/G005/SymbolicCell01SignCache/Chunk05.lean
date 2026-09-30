import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk05
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial060 : Quartic := ⟨-32453668161774863703928366070124500000, -22293570858301424716218882787447792171, 237781757809270444000000000000000000000, -152538216993521680716218882787447792171, 97575904899473003703928366070124500000⟩

theorem sign060 : polynomial060.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial060, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry060 : CachedQuarticSign :=
  ⟨polynomial060, (11/16), (27/32),
    false, .leaf⟩

theorem entry060_checked : entry060.Check := by
  change polynomial060.BernsteinNonnegCheck (11/16) (27/32)
  exact sign060

def polynomial061 : Quartic := ⟨-326153740, 274527857, 326153740, 0, 0⟩

theorem sign061 : polynomial061.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial061, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry061 : CachedQuarticSign :=
  ⟨polynomial061, (11/16), (27/32),
    false, .leaf⟩

theorem entry061_checked : entry061.Check := by
  change polynomial061.BernsteinNonnegCheck (11/16) (27/32)
  exact sign061

def polynomial062 : Quartic := ⟨-326194121720519559815180043394784802941, 1623071291809834248283938821178119328290, -2016749551311249207972785562108730394118, 200975060090165751716061178821880671710, 342622873657814410184819956605215197059⟩

theorem sign062 : polynomial062.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial062, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry062 : CachedQuarticSign :=
  ⟨polynomial062, (1/2), (19/32),
    false, .leaf⟩

theorem entry062_checked : entry062.Check := by
  change polynomial062.BernsteinNonnegCheck (1/2) (19/32)
  exact sign062

def polynomial063 : Quartic := ⟨-3431085921179759239447533472577, -47257382378876147831160535561232, 122239870120000000000000000000000, -62537489338876147831160535561232, 3431093561179759239447533472577⟩

theorem sign063 : polynomial063.BernsteinNonnegCheck (57/64) 1 := by
  norm_num [polynomial063, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry063 : CachedQuarticSign :=
  ⟨polynomial063, (57/64), 1,
    false, .leaf⟩

theorem entry063_checked : entry063.Check := by
  change polynomial063.BernsteinNonnegCheck (57/64) 1
  exact sign063

def polynomial064 : Quartic := ⟨-3431085921179759239447533472577, 13862495381123852168839464438768, 106959900680000000000000000000000, -123657367098876147831160535561232, 3431093561179759239447533472577⟩

theorem sign064 : polynomial064.BernsteinNonnegCheck (27/32) (7/8) := by
  norm_num [polynomial064, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry064 : CachedQuarticSign :=
  ⟨polynomial064, (27/32), (7/8),
    false, .leaf⟩

theorem entry064_checked : entry064.Check := by
  change polynomial064.BernsteinNonnegCheck (27/32) (7/8)
  exact sign064

def polynomial065 : Quartic := ⟨-3431085921179759239447533472577, 7639992360000000000000000000000, -6862179482359518478895066945154, 7639992360000000000000000000000, -3431093561179759239447533472577⟩

theorem sign065 : polynomial065.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial065, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry065 : CachedQuarticSign :=
  ⟨polynomial065, (27/32), 1,
    false, .leaf⟩

theorem entry065_checked : entry065.Check := by
  change polynomial065.BernsteinNonnegCheck (27/32) 1
  exact sign065

def polynomial066 : Quartic := ⟨-36727300204626926682816112762277799, 231610029859534159589402068319000000, -241643659210020000000000000000000000, 148743151859534159589402068319000000, 278370558994606926682816112762277799⟩

theorem sign066 : polynomial066.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial066, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry066 : CachedQuarticSign :=
  ⟨polynomial066, (19/64), (5/16),
    false, .leaf⟩

theorem entry066_checked : entry066.Check := by
  change polynomial066.BernsteinNonnegCheck (19/64) (5/16)
  exact sign066

def polynomial067 : Quartic := ⟨-36926713538830731015468246370679527658392587, -107050927880789146931459113275400563491214826, 248639041517078815187185000000000000000000000, 155698571067561126270200886724599436508785174, -49088624359401822979706753629320472341607413⟩

theorem sign067 : polynomial067.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial067, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry067 : CachedQuarticSign :=
  ⟨polynomial067, (11/16), (27/32),
    false, .leaf⟩

theorem entry067_checked : entry067.Check := by
  change polynomial067.BernsteinNonnegCheck (11/16) (27/32)
  exact sign067

def polynomial068 : Quartic := ⟨-37221992477961185899559499322571, 338251074170836301230759973000000, 490334576607908697467380903754858, -48978852716436301230759973000000, -321722623475561185899559499322571⟩

theorem sign068 : polynomial068.BernsteinNonnegCheck (61/128) (31/64) := by
  norm_num [polynomial068, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry068 : CachedQuarticSign :=
  ⟨polynomial068, (61/128), (31/64),
    false, .leaf⟩

theorem entry068_checked : entry068.Check := by
  change polynomial068.BernsteinNonnegCheck (61/128) (31/64)
  exact sign068

def polynomial069 : Quartic := ⟨-382000000, 827666667, 382000000, 0, 0⟩

theorem sign069 : polynomial069.BernsteinNonnegCheck (101/256) 1 := by
  norm_num [polynomial069, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry069 : CachedQuarticSign :=
  ⟨polynomial069, (101/256), 1,
    false, .leaf⟩

theorem entry069_checked : entry069.Check := by
  change polynomial069.BernsteinNonnegCheck (101/256) 1
  exact sign069

def polynomial070 : Quartic := ⟨-404061508107060683533606876403202193, 2416431119692987365480000000000000000, -1352288751579153318053606876403202193, 0, 0⟩

theorem sign070 : polynomial070.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial070, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry070 : CachedQuarticSign :=
  ⟨polynomial070, (21/64), (91/256),
    false, .leaf⟩

theorem entry070_checked : entry070.Check := by
  change polynomial070.BernsteinNonnegCheck (21/64) (91/256)
  exact sign070

def polynomial071 : Quartic := ⟨-4093, 1069720, 4093, 0, 0⟩

theorem sign071 : polynomial071.BernsteinNonnegCheck (1/256) (91/256) := by
  norm_num [polynomial071, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry071 : CachedQuarticSign :=
  ⟨polynomial071, (1/256), (91/256),
    false, .leaf⟩

theorem entry071_checked : entry071.Check := by
  change polynomial071.BernsteinNonnegCheck (1/256) (91/256)
  exact sign071

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk05
