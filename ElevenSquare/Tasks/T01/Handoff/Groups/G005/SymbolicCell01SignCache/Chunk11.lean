import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk11
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial132 : Quartic := ⟨1, 0, -1, 0, 0⟩

theorem sign132 : polynomial132.BernsteinPosCheck 0 (27/32) := by
  norm_num [polynomial132, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry132 : CachedQuarticSign :=
  ⟨polynomial132, 0, (27/32),
    true, .leaf⟩

theorem entry132_checked : entry132.Check := by
  change polynomial132.BernsteinPosCheck 0 (27/32)
  exact sign132

def polynomial133 : Quartic := ⟨1, 0, 1, 0, 0⟩

theorem sign133 : polynomial133.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial133, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry133 : CachedQuarticSign :=
  ⟨polynomial133, 0, 1,
    false, .leaf⟩

theorem entry133_checked : entry133.Check := by
  change polynomial133.BernsteinNonnegCheck 0 1
  exact sign133

def polynomial134 : Quartic := ⟨1, 0, 1, 0, 0⟩

theorem sign134 : polynomial134.BernsteinPosCheck 0 1 := by
  norm_num [polynomial134, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry134 : CachedQuarticSign :=
  ⟨polynomial134, 0, 1,
    true, .leaf⟩

theorem entry134_checked : entry134.Check := by
  change polynomial134.BernsteinPosCheck 0 1
  exact sign134

def polynomial135 : Quartic := ⟨1, 0, 2, 0, 1⟩

theorem sign135 : polynomial135.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial135, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry135 : CachedQuarticSign :=
  ⟨polynomial135, 0, 1,
    false, .leaf⟩

theorem entry135_checked : entry135.Check := by
  change polynomial135.BernsteinNonnegCheck 0 1
  exact sign135

def polynomial136 : Quartic := ⟨1, 16, -1, 0, 0⟩

theorem sign136 : polynomial136.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial136, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry136 : CachedQuarticSign :=
  ⟨polynomial136, 0, 1,
    false, .leaf⟩

theorem entry136_checked : entry136.Check := by
  change polynomial136.BernsteinNonnegCheck 0 1
  exact sign136

def polynomial137 : Quartic := ⟨100274768003421900815384308039, 3728424117955742555063470000000, -14916175558095240000000000000000, 6638897401765262555063470000000, 3901625990091818099184615691961⟩

theorem sign137 : polynomial137.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial137, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry137 : CachedQuarticSign :=
  ⟨polynomial137, (19/64), (5/16),
    false, .leaf⟩

theorem entry137_checked : entry137.Check := by
  change polynomial137.BernsteinNonnegCheck (19/64) (5/16)
  exact sign137

def polynomial138 : Quartic := ⟨1024696848338586503759272169338250692872634985, -647741475254315193464648255905208069335914246, -6654849492906327936133600000000000000000000000, 2077193104060872536043111744094791930664085754, 2289833960213717561882087830661749307127365015⟩

theorem sign138 : polynomial138.BernsteinNonnegCheck (5/256) (1/4) := by
  norm_num [polynomial138, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry138 : CachedQuarticSign :=
  ⟨polynomial138, (5/256), (1/4),
    false, .leaf⟩

theorem entry138_checked : entry138.Check := by
  change polynomial138.BernsteinNonnegCheck (5/256) (1/4)
  exact sign138

def polynomial139 : Quartic := ⟨104120699124100517729873896694, 12062120459232136197237667362885, -52206614453333340000000000000000, 22248776952565456197237667362885, 13902531954209239482270126103306⟩

theorem sign139 : polynomial139.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial139, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry139 : CachedQuarticSign :=
  ⟨polynomial139, 0, (1/64),
    false, .leaf⟩

theorem entry139_checked : entry139.Check := by
  change polynomial139.BernsteinNonnegCheck 0 (1/64)
  exact sign139

def polynomial140 : Quartic := ⟨104164916563481751620767381553281778212027301, -900967886365704609721726121222195158198721011, -68008125877929691093040000000000000000000000, 673980120460874552493033878777804841801278989, 31405417464526769941512618446718221787972699⟩

theorem sign140 : polynomial140.BernsteinNonnegCheck (5/256) (3/32) := by
  norm_num [polynomial140, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry140 : CachedQuarticSign :=
  ⟨polynomial140, (5/256), (3/32),
    false, .leaf⟩

theorem entry140_checked : entry140.Check := by
  change polynomial140.BernsteinNonnegCheck (5/256) (3/32)
  exact sign140

def polynomial141 : Quartic := ⟨1043628125962023849762821506562408343251337499, -706801370755023258057742188978002795348741700, -6654849492906327936133600000000000000000000000, 2018133208560164471450017811021997204651258300, 2270902682590280215878538493437591656748662501⟩

theorem sign141 : polynomial141.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial141, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry141 : CachedQuarticSign :=
  ⟨polynomial141, (19/64), (5/16),
    false, .leaf⟩

theorem entry141_checked : entry141.Check := by
  change polynomial141.BernsteinNonnegCheck (19/64) (5/16)
  exact sign141

def polynomial142 : Quartic := ⟨104575303912556369706728358827486010220963721, -925423254771217868181053581315322905827956179, -68008125877929691093040000000000000000000000, 649524752055361294033706418684677094172043821, 30995030115452151855551641172513989779036279⟩

theorem sign142 : polynomial142.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial142, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry142 : CachedQuarticSign :=
  ⟨polynomial142, 0, (1/64),
    false, .leaf⟩

theorem entry142_checked : entry142.Check := by
  change polynomial142.BernsteinNonnegCheck 0 (1/64)
  exact sign142

def polynomial143 : Quartic := ⟨104650895259444618666475094419178402685467451, -247132420818892465586400986873920997335464764, 712109803989890373306404000000000000000000000, -737211369372153603349272986873920997335464764, 134201680319986972257200905580821597314532549⟩

theorem sign143 : polynomial143.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial143, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry143 : CachedQuarticSign :=
  ⟨polynomial143, (101/256), (19/32),
    false, .leaf⟩

theorem entry143_checked : entry143.Check := by
  change polynomial143.BernsteinNonnegCheck (101/256) (19/32)
  exact sign143

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk11
