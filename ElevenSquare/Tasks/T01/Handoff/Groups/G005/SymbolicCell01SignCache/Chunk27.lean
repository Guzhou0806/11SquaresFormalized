import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk27
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial324 : Quartic := ⟨710115475966960329782441830289972215, -3073863702038286021257570479427113424, 2702057187547080000000000000000000000, -4351015762038286021257570479427113424, -710116188419880329782441830289972215⟩

theorem sign324 : polynomial324.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial324, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry324 : CachedQuarticSign :=
  ⟨polynomial324, (7/32), (1/4),
    false, .leaf⟩

theorem entry324_checked : entry324.Check := by
  change polynomial324.BernsteinNonnegCheck (7/32) (1/4)
  exact sign324

def polynomial325 : Quartic := ⟨729587363583452316273227726307696089, -1686684688226963626523438688778931560, 39353831124212452767504721084422822, -2368367081653276373476561311221068440, -1329208978815627683726772273692303911⟩

theorem sign325 : polynomial325.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial325, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry325 : CachedQuarticSign :=
  ⟨polynomial325, (19/64), (5/16),
    false, .leaf⟩

theorem entry325_checked : entry325.Check := by
  change polynomial325.BernsteinNonnegCheck (19/64) (5/16)
  exact sign325

def polynomial326 : Quartic := ⟨730042442723262468431957836263761335, -1807040938156640085315604977452523306, 409489925086516226458540793392340570, -2248010831723599914684395022547476694, -1328753899675817531568042163736238665⟩

theorem sign326 : polynomial326.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial326, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry326 : CachedQuarticSign :=
  ⟨polynomial326, (7/32), (1/4),
    false, .leaf⟩

theorem entry326_checked : entry326.Check := by
  change polynomial326.BernsteinNonnegCheck (7/32) (1/4)
  exact sign326

def polynomial327 : Quartic := ⟨7338663700307027346659728325883, 59846616373333330000000000000000, -69061252896359642653340271674117, 0, 0⟩

theorem sign327 : polynomial327.BernsteinNonnegCheck (21/64) (19/32) := by
  norm_num [polynomial327, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry327 : CachedQuarticSign :=
  ⟨polynomial327, (21/64), (19/32),
    false, .leaf⟩

theorem entry327_checked : entry327.Check := by
  change polynomial327.BernsteinNonnegCheck (21/64) (19/32)
  exact sign327

def polynomial328 : Quartic := ⟨734982740175227078444813893536695182511565363, -321224379359898660285593389739120376008000000, -4802056658933740687466360000000000000000000000, -110834007656463670325513389739120376008000000, 969014366570010249021546106463304817488434637⟩

theorem sign328 : polynomial328.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial328, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry328 : CachedQuarticSign :=
  ⟨polynomial328, (19/64), (5/16),
    false, .leaf⟩

theorem entry328_checked : entry328.Check := by
  change polynomial328.BernsteinNonnegCheck (19/64) (5/16)
  exact sign328

def polynomial329 : Quartic := ⟨73672111469285833525300000, -69413382346602358995375389, 0, -69413382346602358995375389, -73672111469285833525300000⟩

theorem sign329 : polynomial329.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial329, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry329 : CachedQuarticSign :=
  ⟨polynomial329, (91/256), (25/64),
    false, .leaf⟩

theorem entry329_checked : entry329.Check := by
  change polynomial329.BernsteinNonnegCheck (91/256) (25/64)
  exact sign329

def polynomial330 : Quartic := ⟨741039, -1048220, -741039, 0, 0⟩

theorem sign330 : polynomial330.BernsteinNonnegCheck (19/64) (91/256) := by
  norm_num [polynomial330, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry330 : CachedQuarticSign :=
  ⟨polynomial330, (19/64), (91/256),
    false, .leaf⟩

theorem entry330_checked : entry330.Check := by
  change polynomial330.BernsteinNonnegCheck (19/64) (91/256)
  exact sign330

def polynomial331 : Quartic := ⟨741039, -1048220, -741039, 0, 0⟩

theorem sign331 : polynomial331.BernsteinPosCheck 0 (5/16) := by
  norm_num [polynomial331, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry331 : CachedQuarticSign :=
  ⟨polynomial331, 0, (5/16),
    true, .leaf⟩

theorem entry331_checked : entry331.Check := by
  change polynomial331.BernsteinPosCheck 0 (5/16)
  exact sign331

def polynomial332 : Quartic := ⟨7447982220106985818860490494377302295983685, -11062710402239605153287658839851917765411491, -36872947049042075832668000000000000000000000, 10186140581764537264500341160148082234588509, 12213522849804228181139509505622697704016315⟩

theorem sign332 : polynomial332.BernsteinNonnegCheck (5/256) (11/64) := by
  norm_num [polynomial332, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry332 : CachedQuarticSign :=
  ⟨polynomial332, (5/256), (11/64),
    false, .leaf⟩

theorem entry332_checked : entry332.Check := by
  change polynomial332.BernsteinNonnegCheck (5/256) (11/64)
  exact sign332

def polynomial333 : Quartic := ⟨7475755663691183895825578811619060113500000, -12717756046977075423965181957065106761683467, -36872947049042075832668000000000000000000000, 8531094937027066993822818042934893238316533, 12185749406220030104174421188380939886500000⟩

theorem sign333 : polynomial333.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial333, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry333 : CachedQuarticSign :=
  ⟨polynomial333, 0, (1/64),
    false, .leaf⟩

theorem entry333_checked : entry333.Check := by
  change polynomial333.BernsteinNonnegCheck 0 (1/64)
  exact sign333

def polynomial334 : Quartic := ⟨7482819984804208563895164063, 5218456817763016000000000000000, -7407192461332499791436104835937, 0, 0⟩

theorem sign334 : polynomial334.BernsteinNonnegCheck 0 (19/32) := by
  norm_num [polynomial334, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry334 : CachedQuarticSign :=
  ⟨polynomial334, 0, (19/32),
    false, .leaf⟩

theorem entry334_checked : entry334.Check := by
  change polynomial334.BernsteinNonnegCheck 0 (19/32)
  exact sign334

def polynomial335 : Quartic := ⟨75340133897605336772156052632748797, 565634666056691069915202896364000000, -205880454633040000000000000000000000, 971140654056691069915202896364000000, 130539503469354663227843947367251203⟩

theorem sign335 : polynomial335.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial335, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry335 : CachedQuarticSign :=
  ⟨polynomial335, 0, 1,
    false, .leaf⟩

theorem entry335_checked : entry335.Check := by
  change polynomial335.BernsteinNonnegCheck 0 1
  exact sign335

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk27
