import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk29
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial348 : Quartic := ⟨85983361156741628221097581431872978981467451, -206686096913413356181012369777187245115275040, 712109803989890373306404000000000000000000000, -696765045466674493943884369777187245115275040, 152869214422689962702578418568127021018532549⟩

theorem sign348 : polynomial348.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial348, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry348 : CachedQuarticSign :=
  ⟨polynomial348, 0, 1,
    false, .leaf⟩

theorem entry348_checked : entry348.Check := by
  change polynomial348.BernsteinNonnegCheck 0 1
  exact sign348

def polynomial349 : Quartic := ⟨880240973003405220900559747509590250000, -486611781157303878713742338732168487980, 198511615868259181363100541996262577489, -562082535189868641286257661267831512020, -365663821982021179099440252490409750000⟩

theorem sign349 : polynomial349.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial349, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry349 : CachedQuarticSign :=
  ⟨polynomial349, (101/256), (19/32),
    false, .leaf⟩

theorem entry349_checked : entry349.Check := by
  change polynomial349.BernsteinNonnegCheck (101/256) (19/32)
  exact sign349

def polynomial350 : Quartic := ⟨888017808955965938936156158547696089, -2027525884940120000000000000000000000, -1170778533443114061063843841452303911, 0, 0⟩

theorem sign350 : polynomial350.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial350, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry350 : CachedQuarticSign :=
  ⟨polynomial350, (21/64), (91/256),
    false, .leaf⟩

theorem entry350_checked : entry350.Check := by
  change polynomial350.BernsteinNonnegCheck (21/64) (91/256)
  exact sign350

def polynomial351 : Quartic := ⟨895649331019165651543209376750895995, 2683301461578345742678999462099069238, -2702061879209960000000000000000000000, 5237605581578345742678999462099069238, 1806404589770874348456790623249104005⟩

theorem sign351 : polynomial351.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial351, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry351 : CachedQuarticSign :=
  ⟨polynomial351, 0, 1,
    false, .leaf⟩

theorem entry351_checked : entry351.Check := by
  change polynomial351.BernsteinNonnegCheck 0 1
  exact sign351

def polynomial352 : Quartic := ⟨90087774823016404729840067086693073793909320285, 387621171321499786512538375078156235949342964706, -169663110748337963203772640000000000000000000000, -1263186172172485958135511224921843764050657035294, 295609758884787432602067612913306926206090679715⟩

theorem sign352 : polynomial352.BernsteinNonnegCheck (101/256) (31/64) := by
  norm_num [polynomial352, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry352 : CachedQuarticSign :=
  ⟨polynomial352, (101/256), (31/64),
    false, .leaf⟩

theorem entry352_checked : entry352.Check := by
  change polynomial352.BernsteinNonnegCheck (101/256) (31/64)
  exact sign352

def polynomial353 : Quartic := ⟨912119792201342328457895993377459127, -1356481715943051261016835918759227880, 2026346982145580000000000000000000000, 24795904056948738983164081240772120, -1602759270055762328457895993377459127⟩

theorem sign353 : polynomial353.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial353, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry353 : CachedQuarticSign :=
  ⟨polynomial353, 0, 1,
    false, .leaf⟩

theorem entry353_checked : entry353.Check := by
  change polynomial353.BernsteinNonnegCheck 0 1
  exact sign353

def polynomial354 : Quartic := ⟨92205872532453940089758755239760787313562313, -234687398067467841849078639258145380671275040, 712109803989890373306404000000000000000000000, -724766346620728979611950639258145380671275040, 146646703046977650833917244760239212686437687⟩

theorem sign354 : polynomial354.BernsteinNonnegCheck (11/16) (499/512) := by
  norm_num [polynomial354, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry354 : CachedQuarticSign :=
  ⟨polynomial354, (11/16), (499/512),
    false, .leaf⟩

theorem entry354_checked : entry354.Check := by
  change polynomial354.BernsteinNonnegCheck (11/16) (499/512)
  exact sign354

def polynomial355 : Quartic := ⟨93253, -520839, -93253, 0, 0⟩

theorem sign355 : polynomial355.BernsteinNonnegCheck 0 (11/64) := by
  norm_num [polynomial355, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry355 : CachedQuarticSign :=
  ⟨polynomial355, 0, (11/64),
    false, .leaf⟩

theorem entry355_checked : entry355.Check := by
  change polynomial355.BernsteinNonnegCheck 0 (11/64)
  exact sign355

def polynomial356 : Quartic := ⟨93253, -520839, -93253, 0, 0⟩

theorem sign356 : polynomial356.BernsteinPosCheck 0 (3/32) := by
  norm_num [polynomial356, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry356 : CachedQuarticSign :=
  ⟨polynomial356, 0, (3/32),
    true, .leaf⟩

theorem entry356_checked : entry356.Check := by
  change polynomial356.BernsteinPosCheck 0 (3/32)
  exact sign356

def polynomial357 : Quartic := ⟨94081214640422898748136151859156922511, 4983619179941705600000000000000000000000, -2003307418053922141251863848140843077489, 0, 0⟩

theorem sign357 : polynomial357.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial357, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry357 : CachedQuarticSign :=
  ⟨polynomial357, 0, 1,
    false, .leaf⟩

theorem entry357_checked : entry357.Check := by
  change polynomial357.BernsteinNonnegCheck 0 1
  exact sign357

def polynomial358 : Quartic := ⟨95500000, 84888889, -95500000, 0, 0⟩

theorem sign358 : polynomial358.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial358, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry358 : CachedQuarticSign :=
  ⟨polynomial358, 0, 1,
    false, .leaf⟩

theorem entry358_checked : entry358.Check := by
  change polynomial358.BernsteinNonnegCheck 0 1
  exact sign358

def polynomial359 : Quartic := ⟨967521109492753839640813073756194387, 10813603261621913313679597619666623296, -11568222293509140000000000000000000000, -9525667199755806686320402380333376704, 383505138449346160359186926243805613⟩

theorem sign359 : polynomial359.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial359, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry359 : CachedQuarticSign :=
  ⟨polynomial359, (91/256), (25/64),
    false, .leaf⟩

theorem entry359_checked : entry359.Check := by
  change polynomial359.BernsteinNonnegCheck (91/256) (25/64)
  exact sign359

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk29
