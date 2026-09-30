import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk20
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial240 : Quartic := ⟨3098803166363802128811341225539, 61083934550040656983595697446042, -76399923600000000000000000000000, -45875958489959343016404302553958, 58021135713636197871188658774461⟩

theorem sign240 : polynomial240.BernsteinNonnegCheck (5/256) (1/4) := by
  norm_num [polynomial240, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry240 : CachedQuarticSign :=
  ⟨polynomial240, (5/256), (1/4),
    false, .leaf⟩

theorem entry240_checked : entry240.Check := by
  change polynomial240.BernsteinNonnegCheck (5/256) (1/4)
  exact sign240

def polynomial241 : Quartic := ⟨3155446415232994176531135316785100715200130427, 4467575555625394442562490684780665903307768260854, -9171838113597232306946145520000000000000000000000, 227220663534467793267059964780665903307768260854, 4697951656357563398170660944683214899284799869573⟩

theorem sign241 : polynomial241.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial241, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry241 : CachedQuarticSign :=
  ⟨polynomial241, (101/256), (19/32),
    false, .leaf⟩

theorem entry241_checked : entry241.Check := by
  change polynomial241.BernsteinNonnegCheck (101/256) (19/32)
  exact sign241

def polynomial242 : Quartic := ⟨318986102500000000000, -487923903061598278737, -4167561103050191190082, 10487913903061598278737, -4681008897500000000000⟩

theorem sign242 : polynomial242.BernsteinNonnegCheck (21/64) (61/128) := by
  norm_num [polynomial242, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry242 : CachedQuarticSign :=
  ⟨polynomial242, (21/64), (61/128),
    false, .leaf⟩

theorem entry242_checked : entry242.Check := by
  change polynomial242.BernsteinNonnegCheck (21/64) (61/128)
  exact sign242

def polynomial243 : Quartic := ⟨3209987906117076538469320691961, 60737071583804703577088858000000, -76399923600000000000000000000000, -46222821456195296422911142000000, 57909950973882923461530679308039⟩

theorem sign243 : polynomial243.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial243, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry243 : CachedQuarticSign :=
  ⟨polynomial243, (19/64), (5/16),
    false, .leaf⟩

theorem entry243_checked : entry243.Check := by
  change polynomial243.BernsteinNonnegCheck (19/64) (5/16)
  exact sign243

def polynomial244 : Quartic := ⟨32107495, -1913315848, -32107495, 0, 0⟩

theorem sign244 : polynomial244.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial244, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry244 : CachedQuarticSign :=
  ⟨polynomial244, 0, (1/64),
    false, .leaf⟩

theorem entry244_checked : entry244.Check := by
  change polynomial244.BernsteinNonnegCheck 0 (1/64)
  exact sign244

def polynomial245 : Quartic := ⟨326153740, -274527857, -326153740, 0, 0⟩

theorem sign245 : polynomial245.BernsteinNonnegCheck 0 (19/32) := by
  norm_num [polynomial245, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry245 : CachedQuarticSign :=
  ⟨polynomial245, 0, (19/32),
    false, .leaf⟩

theorem entry245_checked : entry245.Check := by
  change polynomial245.BernsteinNonnegCheck 0 (19/32)
  exact sign245

def polynomial246 : Quartic := ⟨330040430003386681946393123596797807, 414334923893387365480000000000000000, -2086390689689600683533606876403202193, 0, 0⟩

theorem sign246 : polynomial246.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial246, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry246 : CachedQuarticSign :=
  ⟨polynomial246, (19/64), (5/16),
    false, .leaf⟩

theorem entry246_checked : entry246.Check := by
  change polynomial246.BernsteinNonnegCheck (19/64) (5/16)
  exact sign246

def polynomial247 : Quartic := ⟨33370148277783110541878416756393136472755, 42304123435042084983360160199746089404158, -57943390168632288711200000000000000000000, -59130347020403265432639839800253910595842, 9248221599156661758121583243606863527245⟩

theorem sign247 : polynomial247.BernsteinNonnegCheck (91/256) (31/64) := by
  norm_num [polynomial247, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry247 : CachedQuarticSign :=
  ⟨polynomial247, (91/256), (31/64),
    false, .leaf⟩

theorem entry247_checked : entry247.Check := by
  change polynomial247.BernsteinNonnegCheck (91/256) (31/64)
  exact sign247

def polynomial248 : Quartic := ⟨354876, 540223, -354876, 0, 0⟩

theorem sign248 : polynomial248.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial248, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry248 : CachedQuarticSign :=
  ⟨polynomial248, 0, 1,
    false, .leaf⟩

theorem entry248_checked : entry248.Check := by
  change polynomial248.BernsteinNonnegCheck 0 1
  exact sign248

def polynomial249 : Quartic := ⟨354876, 540223, -354876, 0, 0⟩

theorem sign249 : polynomial249.BernsteinPosCheck 0 1 := by
  norm_num [polynomial249, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry249 : CachedQuarticSign :=
  ⟨polynomial249, 0, 1,
    true, .leaf⟩

theorem entry249_checked : entry249.Check := by
  change polynomial249.BernsteinPosCheck 0 1
  exact sign249

def polynomial250 : Quartic := ⟨364970006867782573901821640411383295, -890164266888900238356849121811384231, 196761774161722382972655409181740150, 2948960609287980238356849121811384231, -648792935602277426098178359588616705⟩

theorem sign250 : polynomial250.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial250, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry250 : CachedQuarticSign :=
  ⟨polynomial250, (91/256), (25/64),
    false, .leaf⟩

theorem entry250_checked : entry250.Check := by
  change polynomial250.BernsteinNonnegCheck (91/256) (25/64)
  exact sign250

def polynomial251 : Quartic := ⟨365857837004883235378757962229246335385, 7280146774069451352369368156317950482014, -14105972565773328240000000000000000000000, -502458771557220407630631843682049517986, 6930334866795116764621242037770753664615⟩

theorem sign251 : polynomial251.BernsteinNonnegCheck (5/256) (1/4) := by
  norm_num [polynomial251, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry251 : CachedQuarticSign :=
  ⟨polynomial251, (5/256), (1/4),
    false, .leaf⟩

theorem entry251_checked : entry251.Check := by
  change polynomial251.BernsteinNonnegCheck (5/256) (1/4)
  exact sign251

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk20
