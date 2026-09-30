import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk24
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial288 : Quartic := ⟨49853054920765498403154072034500000, 953560669292501341795061744062664053, 712450930395020000000000000000000000, -1748497230707498658204938255937335947, 1939749935474254501596845927965500000⟩

theorem sign288 : polynomial288.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial288, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry288 : CachedQuarticSign :=
  ⟨polynomial288, 0, 1,
    false, .leaf⟩

theorem entry288_checked : entry288.Check := by
  change polynomial288.BernsteinNonnegCheck 0 1
  exact sign288

def polynomial289 : Quartic := ⟨50505113318690462982585545079788758993, 6450747594787016905873466885780702482014, -28968992043258987720000000000000000000000, 12795258477149790025873466885780702482014, 7490988606980047737017414454920211241007⟩

theorem sign289 : polynomial289.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial289, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry289 : CachedQuarticSign :=
  ⟨polynomial289, 0, (1/64),
    false, .leaf⟩

theorem entry289_checked : entry289.Check := by
  change polynomial289.BernsteinNonnegCheck 0 (1/64)
  exact sign289

def polynomial290 : Quartic := ⟨5080084569505709412497977484687858461818665, 352996490237891851823495347290723664454298322, -762638922923311875583432000000000000000000000, -460868554590661160380232652709276335545701678, -18300643223425059233417977484687858461818665⟩

theorem sign290 : polynomial290.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial290, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry290 : CachedQuarticSign :=
  ⟨polynomial290, (19/64), (5/16),
    false, .leaf⟩

theorem entry290_checked : entry290.Check := by
  change polynomial290.BernsteinNonnegCheck (19/64) (5/16)
  exact sign290

def polynomial291 : Quartic := ⟨509333333, -509333334, -509333333, 0, 0⟩

theorem sign291 : polynomial291.BernsteinNonnegCheck (91/256) (19/32) := by
  norm_num [polynomial291, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry291 : CachedQuarticSign :=
  ⟨polynomial291, (91/256), (19/32),
    false, .leaf⟩

theorem entry291_checked : entry291.Check := by
  change polynomial291.BernsteinNonnegCheck (91/256) (19/32)
  exact sign291

def polynomial292 : Quartic := ⟨509333333, -509333334, -509333333, 0, 0⟩

theorem sign292 : polynomial292.BernsteinPosCheck (101/256) (19/32) := by
  norm_num [polynomial292, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry292 : CachedQuarticSign :=
  ⟨polynomial292, (101/256), (19/32),
    true, .leaf⟩

theorem entry292_checked : entry292.Check := by
  change polynomial292.BernsteinPosCheck (101/256) (19/32)
  exact sign292

def polynomial293 : Quartic := ⟨511071043209203240658961140669237690996778649, 1376247142793846872806640000000000000000000000, -1878546210646771339341038859330762309003221351, 0, 0⟩

theorem sign293 : polynomial293.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial293, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry293 : CachedQuarticSign :=
  ⟨polynomial293, 0, 1,
    false, .leaf⟩

theorem entry293_checked : entry293.Check := by
  change polynomial293.BernsteinNonnegCheck 0 1
  exact sign293

def polynomial294 : Quartic := ⟨511975090330462770884376220517864795068750709, -1727981671188474975518713268283549159806498582, 1380928584261009122597260000000000000000000000, 539109486172640159484806731716450840193501418, -676897092351198910084636220517864795068750709⟩

theorem sign294 : polynomial294.BernsteinNonnegCheck (3/4) 1 := by
  norm_num [polynomial294, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry294 : CachedQuarticSign :=
  ⟨polynomial294, (3/4), 1,
    false, .leaf⟩

theorem entry294_checked : entry294.Check := by
  change polynomial294.BernsteinNonnegCheck (3/4) 1
  exact sign294

def polynomial295 : Quartic := ⟨513408205666690019566158398222565275307500000, -387024114568784664138156894645297152746033351, -3327424746453163968066800000000000000000000000, 975443175088809200615723105354702847253966649, 1143857198609462013254521601777434724692500000⟩

theorem sign295 : polynomial295.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial295, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry295 : CachedQuarticSign :=
  ⟨polynomial295, 0, (1/64),
    false, .leaf⟩

theorem entry295_checked : entry295.Check := by
  change polynomial295.BernsteinNonnegCheck 0 (1/64)
  exact sign295

def polynomial296 : Quartic := ⟨518541918426987680736622036564, 10057021000393253079815844490859, -12733320600000000000000000000000, -7769627839606746920184155509141, 9668114561573012319263377963436⟩

theorem sign296 : polynomial296.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial296, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry296 : CachedQuarticSign :=
  ⟨polynomial296, 0, (1/64),
    false, .leaf⟩

theorem entry296_checked : entry296.Check := by
  change polynomial296.BernsteinNonnegCheck 0 (1/64)
  exact sign296

def polynomial297 : Quartic := ⟨520839, 373012, -520839, 0, 0⟩

theorem sign297 : polynomial297.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial297, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry297 : CachedQuarticSign :=
  ⟨polynomial297, 0, 1,
    false, .leaf⟩

theorem entry297_checked : entry297.Check := by
  change polynomial297.BernsteinNonnegCheck 0 1
  exact sign297

def polynomial298 : Quartic := ⟨520839, 373012, -520839, 0, 0⟩

theorem sign298 : polynomial298.BernsteinPosCheck 0 1 := by
  norm_num [polynomial298, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry298 : CachedQuarticSign :=
  ⟨polynomial298, 0, 1,
    true, .leaf⟩

theorem entry298_checked : entry298.Check := by
  change polynomial298.BernsteinPosCheck 0 1
  exact sign298

def polynomial299 : Quartic := ⟨52855444604497144902455871609998797, 205879688446090000000000000000000000, -204103271683332855097544128390001203, 0, 0⟩

theorem sign299 : polynomial299.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial299, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry299 : CachedQuarticSign :=
  ⟨polynomial299, 0, 1,
    false, .leaf⟩

theorem entry299_checked : entry299.Check := by
  change polynomial299.BernsteinNonnegCheck 0 1
  exact sign299

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk24
