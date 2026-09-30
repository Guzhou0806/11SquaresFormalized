import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk21
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial252 : Quartic := ⟨368753984016503128567718503777329757, 155346198896579297039874219243605872773, -644718951577546560000000000000000000000, 330575349032968217039874219243605872773, 156127846496369376871432281496222670243⟩

theorem sign252 : polynomial252.BernsteinNonnegCheck (5/256) (1/4) := by
  norm_num [polynomial252, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry252 : CachedQuarticSign :=
  ⟨polynomial252, (5/256), (1/4),
    false, .leaf⟩

theorem entry252_checked : entry252.Check := by
  change polynomial252.BernsteinNonnegCheck (5/256) (1/4)
  exact sign252

def polynomial253 : Quartic := ⟨382000000, -827666667, -382000000, 0, 0⟩

theorem sign253 : polynomial253.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial253, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry253 : CachedQuarticSign :=
  ⟨polynomial253, (91/256), (25/64),
    false, .leaf⟩

theorem entry253_checked : entry253.Check := by
  change polynomial253.BernsteinNonnegCheck (91/256) (25/64)
  exact sign253

def polynomial254 : Quartic := ⟨382000000, -827666667, 0, -827666667, -382000000⟩

theorem sign254 : polynomial254.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial254, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry254 : CachedQuarticSign :=
  ⟨polynomial254, (91/256), (25/64),
    false, .leaf⟩

theorem entry254_checked : entry254.Check := by
  change polynomial254.BernsteinNonnegCheck (91/256) (25/64)
  exact sign254

def polynomial255 : Quartic := ⟨387703331935490209775569872292220447059, -1646587293150986887667875680812972000000, 3029040384616603160000000000000000000000, -1222435514743189447667875680812972000000, -387704195234610089775569872292220447059⟩

theorem sign255 : polynomial255.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial255, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry255 : CachedQuarticSign :=
  ⟨polynomial255, (27/32), 1,
    false, .leaf⟩

theorem entry255_checked : entry255.Check := by
  change polynomial255.BernsteinNonnegCheck (27/32) 1
  exact sign255

def polynomial256 : Quartic := ⟨388906438820240760552466527423, -6726145534470535652604474000000, 7639992360000000000000000000000, -22006145534470535652604474000000, 7251085921179759239447533472577⟩

theorem sign256 : polynomial256.BernsteinNonnegCheck 0 (7/128) := by
  norm_num [polynomial256, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry256 : CachedQuarticSign :=
  ⟨polynomial256, 0, (7/128),
    false, .leaf⟩

theorem entry256_checked : entry256.Check := by
  change polynomial256.BernsteinNonnegCheck 0 (7/128)
  exact sign256

def polynomial257 : Quartic := ⟨38970878626003960542965724564656349287491648559379, 400801029958162786940744689868250000000000000000000, -180060397433742423754489607002093650712508351440621, 0, 0⟩

theorem sign257 : polynomial257.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial257, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry257 : CachedQuarticSign :=
  ⟨polynomial257, 0, 1,
    false, .leaf⟩

theorem entry257_checked : entry257.Check := by
  change polynomial257.BernsteinNonnegCheck 0 1
  exact sign257

def polynomial258 : Quartic := ⟨390192617893498360962994133943927828078500460, 2192606307257899413815908037444359491147224621, 1587627422067330802949080000000000000000000000, -1050259839598462962928931962555640508852775379, -349979342481958837465394133943927828078500460⟩

theorem sign258 : polynomial258.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial258, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry258 : CachedQuarticSign :=
  ⟨polynomial258, 0, 1,
    false, .leaf⟩

theorem entry258_checked : entry258.Check := by
  change polynomial258.BernsteinNonnegCheck 0 1
  exact sign258

def polynomial259 : Quartic := ⟨390857510920412472138579145256243985, -872878525452909743786564420026742339, 29310674962358206543468173939419530, 2931674867851989743786564420026742339, -622905431549647527861420854743756015⟩

theorem sign259 : polynomial259.BernsteinNonnegCheck (11/16) (115/128) := by
  norm_num [polynomial259, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry259 : CachedQuarticSign :=
  ⟨polynomial259, (11/16), (115/128),
    false, .leaf⟩

theorem entry259_checked : entry259.Check := by
  change polynomial259.BernsteinNonnegCheck (11/16) (115/128)
  exact sign259

def polynomial260 : Quartic := ⟨397086194681564067017829633292365326583627323, 5439094248955350667191630905608288104124433584, 1613730765972487899050440000000000000000000000, -4660582771963225906773969094391711895875566416, -535831653408922929355229633292365326583627323⟩

theorem sign260 : polynomial260.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial260, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry260 : CachedQuarticSign :=
  ⟨polynomial260, 0, 1,
    false, .leaf⟩

theorem entry260_checked : entry260.Check := by
  change polynomial260.BernsteinNonnegCheck 0 1
  exact sign260

def polynomial261 : Quartic := ⟨4, -1, -4, 0, 0⟩

theorem sign261 : polynomial261.BernsteinNonnegCheck 0 (5/16) := by
  norm_num [polynomial261, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry261 : CachedQuarticSign :=
  ⟨polynomial261, 0, (5/16),
    false, .leaf⟩

theorem entry261_checked : entry261.Check := by
  change polynomial261.BernsteinNonnegCheck 0 (5/16)
  exact sign261

def polynomial262 : Quartic := ⟨408012994124436174907103508460308907616701335, -3943574904203370516441122299058157437289689746, -878967319321422860845240000000000000000000000, 3006206103062047733094957700941842562710310254, 58338991442111300324856491539691092383298665⟩

theorem sign262 : polynomial262.BernsteinNonnegCheck (5/256) (3/32) := by
  norm_num [polynomial262, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry262 : CachedQuarticSign :=
  ⟨polynomial262, (5/256), (3/32),
    false, .leaf⟩

theorem entry262_checked : entry262.Check := by
  change polynomial262.BernsteinNonnegCheck (5/256) (3/32)
  exact sign262

def polynomial263 : Quartic := ⟨4093, -1069720, -4093, 0, 0⟩

theorem sign263 : polynomial263.BernsteinNonnegCheck 0 (1/512) := by
  norm_num [polynomial263, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry263 : CachedQuarticSign :=
  ⟨polynomial263, 0, (1/512),
    false, .leaf⟩

theorem entry263_checked : entry263.Check := by
  change polynomial263.BernsteinNonnegCheck 0 (1/512)
  exact sign263

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk21
