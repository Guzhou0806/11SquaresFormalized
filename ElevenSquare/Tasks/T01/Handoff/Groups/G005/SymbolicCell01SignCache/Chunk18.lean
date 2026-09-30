import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk18
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial216 : Quartic := ⟨243705382310000000000000000000, -101248774647032785071551472577, -3924539648424703577088858000000, 7741241134647032785071551472577, -3576290797690000000000000000000⟩

theorem sign216 : polynomial216.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial216, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry216 : CachedQuarticSign :=
  ⟨polynomial216, (19/64), (5/16),
    false, .leaf⟩

theorem entry216_checked : entry216.Check := by
  change polynomial216.BernsteinNonnegCheck (19/64) (5/16)
  exact sign216

def polynomial217 : Quartic := ⟨243705382310000000000000000000, 9935965106241624586427993845, -4271402614660656983595697446042, 7630056394893758375413572006155, -3576290797690000000000000000000⟩

theorem sign217 : polynomial217.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial217, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry217 : CachedQuarticSign :=
  ⟨polynomial217, (7/32), (1/4),
    false, .leaf⟩

theorem entry217_checked : entry217.Check := by
  change polynomial217.BernsteinNonnegCheck (7/32) (1/4)
  exact sign217

def polynomial218 : Quartic := ⟨243722105369430854094286744174806146421202491433506863, -553467256476004444786075866767272000000000000000000000, -318281256330735176444141505173441853578797508566493137, 0, 0⟩

theorem sign218 : polynomial218.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial218, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry218 : CachedQuarticSign :=
  ⟨polynomial218, (21/64), (91/256),
    false, .leaf⟩

theorem entry218_checked : entry218.Check := by
  change polynomial218.BernsteinNonnegCheck (21/64) (91/256)
  exact sign218

def polynomial219 : Quartic := ⟨2476483411092364020675514470822789312951, 21731946214595346240000000000000000000000, -24863966059394036379324485529177210687049, 0, 0⟩

theorem sign219 : polynomial219.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial219, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry219 : CachedQuarticSign :=
  ⟨polynomial219, (11/16), (27/32),
    false, .leaf⟩

theorem entry219_checked : entry219.Check := by
  change polynomial219.BernsteinNonnegCheck (11/16) (27/32)
  exact sign219

def polynomial220 : Quartic := ⟨24817931571412740850318685603408488611629000000, -423300257370778865112071035379416439640059482353, 1052485148082123383641006200000000000000000000000, -440621055490586382125991115379416439640059482353, -252854069069455095291324885603408488611629000000⟩

theorem sign220 : polynomial220.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial220, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry220 : CachedQuarticSign :=
  ⟨polynomial220, (11/16), (27/32),
    false, .leaf⟩

theorem entry220_checked : entry220.Check := by
  change polynomial220.BernsteinNonnegCheck (11/16) (27/32)
  exact sign220

def polynomial221 : Quartic := ⟨25025406229494411999647065965, 14115116778684046507629018892, 7589933907541011176000705868070, -14115116778684046507629018892, -7614959313770505588000352934035⟩

theorem sign221 : polynomial221.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial221, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry221 : CachedQuarticSign :=
  ⟨polynomial221, 0, 1,
    false, .leaf⟩

theorem entry221_checked : entry221.Check := by
  change polynomial221.BernsteinNonnegCheck 0 1
  exact sign221

def polynomial222 : Quartic := ⟨252714695634040692038188700763960785, 4272997693325337021850483224811899754, 3666685950779924668437256723838614998, -5568196662922217021850483224811899754, -4522180254556959307961811299236039215⟩

theorem sign222 : polynomial222.BernsteinNonnegCheck (5/256) (7/128) := by
  norm_num [polynomial222, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry222 : CachedQuarticSign :=
  ⟨polynomial222, (5/256), (7/128),
    false, .leaf⟩

theorem entry222_checked : entry222.Check := by
  change polynomial222.BernsteinNonnegCheck (5/256) (7/128)
  exact sign222

def polynomial223 : Quartic := ⟨254666667, 1018666666, -254666667, 0, 0⟩

theorem sign223 : polynomial223.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial223, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry223 : CachedQuarticSign :=
  ⟨polynomial223, 0, 1,
    false, .leaf⟩

theorem entry223_checked : entry223.Check := by
  change polynomial223.BernsteinNonnegCheck 0 1
  exact sign223

def polynomial224 : Quartic := ⟨254666667, 1018666666, -254666667, 0, 0⟩

theorem sign224 : polynomial224.BernsteinPosCheck 0 1 := by
  norm_num [polynomial224, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry224 : CachedQuarticSign :=
  ⟨polynomial224, 0, 1,
    true, .leaf⟩

theorem entry224_checked : entry224.Check := by
  change polynomial224.BernsteinPosCheck 0 1
  exact sign224

def polynomial225 : Quartic := ⟨262055, 741039, -262055, 0, 0⟩

theorem sign225 : polynomial225.BernsteinPosCheck 0 1 := by
  norm_num [polynomial225, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry225 : CachedQuarticSign :=
  ⟨polynomial225, 0, 1,
    true, .leaf⟩

theorem entry225_checked : entry225.Check := by
  change polynomial225.BernsteinPosCheck 0 1
  exact sign225

def polynomial226 : Quartic := ⟨267430, 4093, -267430, 0, 0⟩

theorem sign226 : polynomial226.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial226, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry226 : CachedQuarticSign :=
  ⟨polynomial226, 0, 1,
    false, .leaf⟩

theorem entry226_checked : entry226.Check := by
  change polynomial226.BernsteinNonnegCheck 0 1
  exact sign226

def polynomial227 : Quartic := ⟨267430, 4093, -267430, 0, 0⟩

theorem sign227 : polynomial227.BernsteinPosCheck 0 1 := by
  norm_num [polynomial227, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry227 : CachedQuarticSign :=
  ⟨polynomial227, 0, 1,
    true, .leaf⟩

theorem entry227_checked : entry227.Check := by
  change polynomial227.BernsteinPosCheck 0 1
  exact sign227

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk18
