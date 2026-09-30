import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk08
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial096 : Quartic := ⟨-62094867436705739995272106152343000000, 496631654656505290677781975951181039145, -451558559350001169728923986107576894118, 366665738625254949322218024048818960855, -387705725513687139995272106152343000000⟩

theorem sign096 : polynomial096.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial096, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry096 : CachedQuarticSign :=
  ⟨polynomial096, (1/2), (19/32),
    false, .leaf⟩

theorem entry096_checked : entry096.Check := by
  change polynomial096.BernsteinNonnegCheck (1/2) (19/32)
  exact sign096

def polynomial097 : Quartic := ⟨-622777140609260081227283685310205668246000000, 1837221583039325219595641772995221954245221351, -24870021212242115231960000000000000000000000, -1374919422639834132365758227004778045754778649, -409406912818504318772716314689794331754000000⟩

theorem sign097 : polynomial097.BernsteinNonnegCheck (101/256) (61/128) := by
  norm_num [polynomial097, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry097 : CachedQuarticSign :=
  ⟨polynomial097, (101/256), (61/128),
    false, .leaf⟩

theorem entry097_checked : entry097.Check := by
  change polynomial097.BernsteinNonnegCheck (101/256) (61/128)
  exact sign097

def polynomial098 : Quartic := ⟨-628361990444224462472701122081735326845959537, 1564392336398997001534247447749209577558967570, 3975503405746349401874120000000000000000000000, -705685779111617526613992552250790422441032430, -648026609049386645695978877918264673154040463⟩

theorem sign098 : polynomial098.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial098, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry098 : CachedQuarticSign :=
  ⟨polynomial098, (19/64), (5/16),
    false, .leaf⟩

theorem entry098_checked : entry098.Check := by
  change polynomial098.BernsteinNonnegCheck (19/64) (5/16)
  exact sign098

def polynomial099 : Quartic := ⟨-6300996046865453879441591311309321797219105, 388502040642786826453469725584858832018852792, -762638922923311875583432000000000000000000000, -425363004185766185750258274415141167981147208, -6919562607053895941478408688690678202780895⟩

theorem sign099 : polynomial099.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial099, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry099 : CachedQuarticSign :=
  ⟨polynomial099, (7/32), (1/4),
    false, .leaf⟩

theorem entry099_checked : entry099.Check := by
  change polynomial099.BernsteinNonnegCheck (7/32) (1/4)
  exact sign099

def polynomial100 : Quartic := ⟨-6381792067814815674641359914744058416801482353, 338070719291022326233076628697693632060245035294, 108017210828511220910104720000000000000000000000, -765013274684041446358788331302306367939754964706, -433324346622595935471438560085255941583198517647⟩

theorem sign100 : polynomial100.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial100, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry100 : CachedQuarticSign :=
  ⟨polynomial100, (1/2), (19/32),
    false, .leaf⟩

theorem entry100_checked : entry100.Check := by
  change polynomial100.BernsteinNonnegCheck (1/2) (19/32)
  exact sign100

def polynomial101 : Quartic := ⟨-6512390434590426701262818042934893238316533, 11828863498946450001090315246476240454000000, 95857462258775717832668000000000000000000000, -30668838469061834834485684753523759546000000, -10699051544540435131405181957065106761683467⟩

theorem sign101 : polynomial101.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial101, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry101 : CachedQuarticSign :=
  ⟨polynomial101, (27/32), 1,
    false, .leaf⟩

theorem entry101_checked : entry101.Check := by
  change polynomial101.BernsteinNonnegCheck (27/32) 1
  exact sign101

def polynomial102 : Quartic := ⟨-700333333, 1910000000, 700333333, 0, 0⟩

theorem sign102 : polynomial102.BernsteinNonnegCheck (21/64) (27/32) := by
  norm_num [polynomial102, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry102 : CachedQuarticSign :=
  ⟨polynomial102, (21/64), (27/32),
    false, .leaf⟩

theorem entry102_checked : entry102.Check := by
  change polynomial102.BernsteinNonnegCheck (21/64) (27/32)
  exact sign102

def polynomial103 : Quartic := ⟨-700333333, 1910000000, 700333333, 0, 0⟩

theorem sign103 : polynomial103.BernsteinPosCheck (21/64) (27/32) := by
  norm_num [polynomial103, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry103 : CachedQuarticSign :=
  ⟨polynomial103, (21/64), (27/32),
    true, .leaf⟩

theorem entry103_checked : entry103.Check := by
  change polynomial103.BernsteinPosCheck (21/64) (27/32)
  exact sign103

def polynomial104 : Quartic := ⟨-72431832551579879718678517346901750000, 309819409162421794967387699631825987980, 1788859421585353517444457677018079422511, 2365448572350914085032612300368174012020, -1896478184451579879718678517346901750000⟩

theorem sign104 : polynomial104.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial104, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry104 : CachedQuarticSign :=
  ⟨polynomial104, (91/256), (25/64),
    false, .leaf⟩

theorem entry104_checked : entry104.Check := by
  change polynomial104.BernsteinNonnegCheck (91/256) (25/64)
  exact sign104

def polynomial105 : Quartic := ⟨-741039, 1048220, 741039, 0, 0⟩

theorem sign105 : polynomial105.BernsteinNonnegCheck (3/4) (115/128) := by
  norm_num [polynomial105, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry105 : CachedQuarticSign :=
  ⟨polynomial105, (3/4), (115/128),
    false, .leaf⟩

theorem entry105_checked : entry105.Check := by
  change polynomial105.BernsteinNonnegCheck (3/4) (115/128)
  exact sign105

def polynomial106 : Quartic := ⟨-742421894984553294832155100900083367, 5610288321372302611096000000000000000, -3169348615092791905928155100900083367, 0, 0⟩

theorem sign106 : polynomial106.BernsteinNonnegCheck (101/256) 1 := by
  norm_num [polynomial106, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry106 : CachedQuarticSign :=
  ⟨polynomial106, (101/256), 1,
    false, .leaf⟩

theorem entry106_checked : entry106.Check := by
  change polynomial106.BernsteinNonnegCheck (101/256) 1
  exact sign106

def polynomial107 : Quartic := ⟨-75088028660616977641562427260115230, 1256590469204625399710119620002713943, 2326162402324776847819830059120093262, 124684388240134600289880379997286057, -1433578541674156977641562427260115230⟩

theorem sign107 : polynomial107.BernsteinNonnegCheck (1/16) (11/64) := by
  norm_num [polynomial107, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry107 : CachedQuarticSign :=
  ⟨polynomial107, (1/16), (11/64),
    false, .leaf⟩

theorem entry107_checked : entry107.Check := by
  change polynomial107.BernsteinNonnegCheck (1/16) (11/64)
  exact sign107

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk08
