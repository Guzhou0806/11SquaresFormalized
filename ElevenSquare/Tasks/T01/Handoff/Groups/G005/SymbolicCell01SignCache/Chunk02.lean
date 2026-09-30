import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk02
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial024 : Quartic := ⟨-14260495822818620831087291312622899947, -12358973683880133297396661001966399152, 51782406854979160000000000000000000000, -8766018749804373297396661001966399152, -12940183795713339168912708687377100053⟩

theorem sign024 : polynomial024.BernsteinNonnegCheck (57/64) 1 := by
  norm_num [polynomial024, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry024 : CachedQuarticSign :=
  ⟨polynomial024, (57/64), 1,
    false, .leaf⟩

theorem entry024_checked : entry024.Check := by
  change polynomial024.BernsteinNonnegCheck (57/64) 1
  exact sign024

def polynomial025 : Quartic := ⟨-1426761021080665863190108021104, 4083516482138220939947868670593, 413001432533096000000000000000, -1134935943179083060052131329407, 4035988331850745863190108021104⟩

theorem sign025 : polynomial025.BernsteinNonnegCheck (61/128) (19/32) := by
  norm_num [polynomial025, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry025 : CachedQuarticSign :=
  ⟨polynomial025, (61/128), (19/32),
    false, .leaf⟩

theorem entry025_checked : entry025.Check := by
  change polynomial025.BernsteinNonnegCheck (61/128) (19/32)
  exact sign025

def polynomial026 : Quartic := ⟨-143387081, 447324591, 143387081, 0, 0⟩

theorem sign026 : polynomial026.BernsteinNonnegCheck (19/64) (27/32) := by
  norm_num [polynomial026, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry026 : CachedQuarticSign :=
  ⟨polynomial026, (19/64), (27/32),
    false, .leaf⟩

theorem entry026_checked : entry026.Check := by
  change polynomial026.BernsteinNonnegCheck (19/64) (27/32)
  exact sign026

def polynomial027 : Quartic := ⟨-143387081, 447324591, 143387081, 0, 0⟩

theorem sign027 : polynomial027.BernsteinPosCheck (11/16) (27/32) := by
  norm_num [polynomial027, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry027 : CachedQuarticSign :=
  ⟨polynomial027, (11/16), (27/32),
    true, .leaf⟩

theorem entry027_checked : entry027.Check := by
  change polynomial027.BernsteinPosCheck (11/16) (27/32)
  exact sign027

def polynomial028 : Quartic := ⟨-145000183863209436103658773571177761, 159643688211985000000000000000000000, 47756194259106127792682452857644478, 159643688211985000000000000000000000, 192756378122315563896341226428822239⟩

theorem sign028 : polynomial028.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial028, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry028 : CachedQuarticSign :=
  ⟨polynomial028, (11/16), (27/32),
    false, .leaf⟩

theorem entry028_checked : entry028.Check := by
  change polynomial028.BernsteinNonnegCheck (11/16) (27/32)
  exact sign028

def polynomial029 : Quartic := ⟨-151603526888546929316092072122774480009392587, 348593728997359856037186742479050476490000000, 178328894825153440187185000000000000000000000, -257379397962467151953163257520949523510000000, -172886870812607291688732927877225519990607413⟩

theorem sign029 : polynomial029.BernsteinNonnegCheck (11/16) (29/32) := by
  norm_num [polynomial029, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry029 : CachedQuarticSign :=
  ⟨polynomial029, (11/16), (29/32),
    false, .leaf⟩

theorem entry029_checked : entry029.Check := by
  change polynomial029.BernsteinNonnegCheck (11/16) (29/32)
  exact sign029

def polynomial030 : Quartic := ⟨-1529120626682808008107037164094327490859, -3148484178466676027344788932622070000000, 14592382002706664120000000000000000000000, -9958278632840004267344788932622070000000, 1529124031576143888107037164094327490859⟩

theorem sign030 : polynomial030.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial030, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry030 : CachedQuarticSign :=
  ⟨polynomial030, (27/32), 1,
    false, .leaf⟩

theorem entry030_checked : entry030.Check := by
  change polynomial030.BernsteinNonnegCheck (27/32) 1
  exact sign030

def polynomial031 : Quartic := ⟨-1534809106377594039264338976579316241007, 1248068254415888250419547433085361517986, 4381901395890929400000000000000000000000, -5587049042853556629580452566914638482014, 1534812523937469279264338976579316241007⟩

theorem sign031 : polynomial031.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial031, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry031 : CachedQuarticSign :=
  ⟨polynomial031, (27/32), 1,
    false, .leaf⟩

theorem entry031_checked : entry031.Check := by
  change polynomial031.BernsteinNonnegCheck (27/32) 1
  exact sign031

def polynomial032 : Quartic := ⟨-161922495093466674202560567485040390094875, 205819703112054095014617135509477386064903153, 381488786848881014038660000000000000000000000, -274362701105552496313862864490522613935096847, -102698887080777067523537439432514959609905125⟩

theorem sign032 : polynomial032.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial032, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry032 : CachedQuarticSign :=
  ⟨polynomial032, (11/16), (27/32),
    false, .leaf⟩

theorem entry032_checked : entry032.Check := by
  change polynomial032.BernsteinNonnegCheck (11/16) (27/32)
  exact sign032

def polynomial033 : Quartic := ⟨-1641187767210728052414848139398011875074, 3544266041187880806118234516266901335385, 245297362065468520000000000000000000000, -3764593434606841633881765483733098664615, 1641191421643997732414848139398011875074⟩

theorem sign033 : polynomial033.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial033, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry033 : CachedQuarticSign :=
  ⟨polynomial033, (27/32), 1,
    false, .leaf⟩

theorem entry033_checked : entry033.Check := by
  change polynomial033.BernsteinNonnegCheck (27/32) 1
  exact sign033

def polynomial034 : Quartic := ⟨-16948941342384027162397302882, 31880924431578689382889136921, 51183919361484000000000000000, -112290481942325310617110863079, 47944770346524027162397302882⟩

theorem sign034 : polynomial034.BernsteinNonnegCheck (61/128) (31/64) := by
  norm_num [polynomial034, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry034 : CachedQuarticSign :=
  ⟨polynomial034, (61/128), (31/64),
    false, .leaf⟩

theorem entry034_checked : entry034.Check := by
  change polynomial034.BernsteinNonnegCheck (61/128) (31/64)
  exact sign034

def polynomial035 : Quartic := ⟨-17155429605898796197237667362885, 10603167303163042070919495586776, 56026572413333360000000000000000, -65796812323503597929080504413224, 17155467805898796197237667362885⟩

theorem sign035 : polynomial035.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial035, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry035 : CachedQuarticSign :=
  ⟨polynomial035, (27/32), 1,
    false, .leaf⟩

theorem entry035_checked : entry035.Check := by
  change polynomial035.BernsteinNonnegCheck (27/32) 1
  exact sign035

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk02
