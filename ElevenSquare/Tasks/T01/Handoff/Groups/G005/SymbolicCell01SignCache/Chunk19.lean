import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk19
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial228 : Quartic := ⟨26764938826371806475473013640118426546503131, -542639334961106918888854122590312141800051500, 307103115412582019917480000000000000000000000, 306859437468552459906665877409687858199948500, 129315345040700676995446986359881573453496869⟩

theorem sign228 : polynomial228.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial228, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry228 : CachedQuarticSign :=
  ⟨polynomial228, (27/32), 1,
    false, .leaf⟩

theorem entry228_checked : entry228.Check := by
  change polynomial228.BernsteinNonnegCheck (27/32) 1
  exact sign228

def polynomial229 : Quartic := ⟨268211, -174831, -268211, 0, 0⟩

theorem sign229 : polynomial229.BernsteinNonnegCheck (1/16) (31/64) := by
  norm_num [polynomial229, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry229 : CachedQuarticSign :=
  ⟨polynomial229, (1/16), (31/64),
    false, .leaf⟩

theorem entry229_checked : entry229.Check := by
  change polynomial229.BernsteinNonnegCheck (1/16) (31/64)
  exact sign229

def polynomial230 : Quartic := ⟨268211, -174831, -268211, 0, 0⟩

theorem sign230 : polynomial230.BernsteinPosCheck (91/256) (19/32) := by
  norm_num [polynomial230, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry230 : CachedQuarticSign :=
  ⟨polynomial230, (91/256), (19/32),
    true, .leaf⟩

theorem entry230_checked : entry230.Check := by
  change polynomial230.BernsteinPosCheck (91/256) (19/32)
  exact sign230

def polynomial231 : Quartic := ⟨26883256634235689008693707833918330801113, 60769194812088597610400000000000000000000, -600038601870260908601706292166081669198887, 0, 0⟩

theorem sign231 : polynomial231.BernsteinNonnegCheck (7/64) (1/4) := by
  norm_num [polynomial231, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry231 : CachedQuarticSign :=
  ⟨polynomial231, (7/64), (1/4),
    false, .leaf⟩

theorem entry231_checked : entry231.Check := by
  change polynomial231.BernsteinNonnegCheck (7/64) (1/4)
  exact sign231

def polynomial232 : Quartic := ⟨274527857, 1304614960, -274527857, 0, 0⟩

theorem sign232 : polynomial232.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial232, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry232 : CachedQuarticSign :=
  ⟨polynomial232, 0, 1,
    false, .leaf⟩

theorem entry232_checked : entry232.Check := by
  change polynomial232.BernsteinNonnegCheck 0 1
  exact sign232

def polynomial233 : Quartic := ⟨2822260472098824318869843760435500000, -6223528563096690464388052196835188691, 10430006390619543000000000000000000000, 336092876638946535611947803164811309, -8485469748883884318869843760435500000⟩

theorem sign233 : polynomial233.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial233, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry233 : CachedQuarticSign :=
  ⟨polynomial233, (11/16), (27/32),
    false, .leaf⟩

theorem entry233_checked : entry233.Check := by
  change polynomial233.BernsteinNonnegCheck (11/16) (27/32)
  exact sign233

def polynomial234 : Quartic := ⟨28425437723387505550776469352421964549987125, 263649896214579279958866986359881573453496869, 40284434047158857623820000000000000000000000, -161099490000250409438893013640118426546503131, 87370412096526120296323530647578035450012875⟩

theorem sign234 : polynomial234.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial234, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry234 : CachedQuarticSign :=
  ⟨polynomial234, 0, 1,
    false, .leaf⟩

theorem entry234_checked : entry234.Check := by
  change polynomial234.BernsteinNonnegCheck 0 1
  exact sign234

def polynomial235 : Quartic := ⟨290023, -1035352, -290023, 0, 0⟩

theorem sign235 : polynomial235.BernsteinPosCheck (7/64) (11/64) := by
  norm_num [polynomial235, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry235 : CachedQuarticSign :=
  ⟨polynomial235, (7/64), (11/64),
    true, .leaf⟩

theorem entry235_checked : entry235.Check := by
  change polynomial235.BernsteinPosCheck (7/64) (11/64)
  exact sign235

def polynomial236 : Quartic := ⟨292413269506696022760535455885, -3448219116723537287208591877303, 11778312001666670000000000000000, -12998216570056867287208591877303, 4482581955493303977239464544115⟩

theorem sign236 : polynomial236.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial236, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry236 : CachedQuarticSign :=
  ⟨polynomial236, (11/16), (27/32),
    false, .leaf⟩

theorem entry236_checked : entry236.Check := by
  change polynomial236.BernsteinNonnegCheck (11/16) (27/32)
  exact sign236

def polynomial237 : Quartic := ⟨29345337882053115167237500000, 132742972333541981121096000000, -1579782326943865469782008472577, 3687253207666458018878904000000, -1880652752117946884832762500000⟩

theorem sign237 : polynomial237.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial237, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry237 : CachedQuarticSign :=
  ⟨polynomial237, 0, (1/64),
    false, .leaf⟩

theorem entry237_checked : entry237.Check := by
  change polynomial237.BernsteinNonnegCheck 0 (1/64)
  exact sign237

def polynomial238 : Quartic := ⟨29816567334025940730524275048540875765, 42431544786036791175167870824708870294, 8777631011075001600000000000000000000000, -17965122472992393368824832129175291129706, 9200105987059399419269475724951459124235⟩

theorem sign238 : polynomial238.BernsteinNonnegCheck (5/256) (11/64) := by
  norm_num [polynomial238, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry238 : CachedQuarticSign :=
  ⟨polynomial238, (5/256), (11/64),
    false, .leaf⟩

theorem entry238_checked : entry238.Check := by
  change polynomial238.BernsteinNonnegCheck (5/256) (11/64)
  exact sign238

def polynomial239 : Quartic := ⟨307281024942964556725, -548563027120915139743, -14732917642086693873778, 40548523027120915139743, -19692698975057035443275⟩

theorem sign239 : polynomial239.BernsteinNonnegCheck (61/128) (31/64) := by
  norm_num [polynomial239, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry239 : CachedQuarticSign :=
  ⟨polynomial239, (61/128), (31/64),
    false, .leaf⟩

theorem entry239_checked : entry239.Check := by
  change polynomial239.BernsteinNonnegCheck (61/128) (31/64)
  exact sign239

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk19
