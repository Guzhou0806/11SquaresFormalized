import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk23
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial276 : Quartic := ⟨4584000000, -700333333, -9168000000, 700333333, 4584000000⟩

theorem sign276 : polynomial276.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial276, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry276 : CachedQuarticSign :=
  ⟨polynomial276, (11/16), (27/32),
    false, .leaf⟩

theorem entry276_checked : entry276.Check := by
  change polynomial276.BernsteinNonnegCheck (11/16) (27/32)
  exact sign276

def polynomial277 : Quartic := ⟨46198114904781351720972736230153603649391512506009579, 574200508270567831946615002051160000000000000000000000, 99017809404419604120166403719313603649391512506009579, 0, 0⟩

theorem sign277 : polynomial277.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial277, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry277 : CachedQuarticSign :=
  ⟨polynomial277, 0, 1,
    false, .leaf⟩

theorem entry277_checked : entry277.Check := by
  change polynomial277.BernsteinNonnegCheck 0 1
  exact sign277

def polynomial278 : Quartic := ⟨46264829103920136020319886788692797290376919947, 361857078689786357124976185376000000000000000000, -183820488954229612659951927835307202709623080053, 0, 0⟩

theorem sign278 : polynomial278.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial278, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry278 : CachedQuarticSign :=
  ⟨polynomial278, 0, 1,
    false, .leaf⟩

theorem entry278_checked : entry278.Check := by
  change polynomial278.BernsteinNonnegCheck 0 1
  exact sign278

def polynomial279 : Quartic := ⟨477500000, -445666667, -477500000, 0, 0⟩

theorem sign279 : polynomial279.BernsteinNonnegCheck 0 (5/16) := by
  norm_num [polynomial279, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry279 : CachedQuarticSign :=
  ⟨polynomial279, 0, (5/16),
    false, .leaf⟩

theorem entry279_checked : entry279.Check := by
  change polynomial279.BernsteinNonnegCheck 0 (5/16)
  exact sign279

def polynomial280 : Quartic := ⟨477500000, 700333333, -477500000, 0, 0⟩

theorem sign280 : polynomial280.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial280, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry280 : CachedQuarticSign :=
  ⟨polynomial280, 0, 1,
    false, .leaf⟩

theorem entry280_checked : entry280.Check := by
  change polynomial280.BernsteinNonnegCheck 0 1
  exact sign280

def polynomial281 : Quartic := ⟨477500000, 700333333, -477500000, 0, 0⟩

theorem sign281 : polynomial281.BernsteinPosCheck 0 1 := by
  norm_num [polynomial281, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry281 : CachedQuarticSign :=
  ⟨polynomial281, 0, 1,
    true, .leaf⟩

theorem entry281_checked : entry281.Check := by
  change polynomial281.BernsteinPosCheck 0 1
  exact sign281

def polynomial282 : Quartic := ⟨478328962, 32107495, -478328962, 0, 0⟩

theorem sign282 : polynomial282.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial282, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry282 : CachedQuarticSign :=
  ⟨polynomial282, 0, 1,
    false, .leaf⟩

theorem entry282_checked : entry282.Check := by
  change polynomial282.BernsteinNonnegCheck 0 1
  exact sign282

def polynomial283 : Quartic := ⟨478328962, 32107495, 0, 32107495, -478328962⟩

theorem sign283 : polynomial283.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial283, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry283 : CachedQuarticSign :=
  ⟨polynomial283, 0, 1,
    false, .leaf⟩

theorem entry283_checked : entry283.Check := by
  change polynomial283.BernsteinNonnegCheck 0 1
  exact sign283

def polynomial284 : Quartic := ⟨47918698625494991548909713764218541912550359163, 2490404668602859452763432187487645306228292718326, -3606593315192578368369688720000000000000000000000, -1517972121058099702972534052512354693771707281674, 1020351244261028537926308606235781458087449640837⟩

theorem sign284 : polynomial284.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial284, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry284 : CachedQuarticSign :=
  ⟨polynomial284, (101/256), (19/32),
    false, .leaf⟩

theorem entry284_checked : entry284.Check := by
  change polynomial284.BernsteinNonnegCheck (101/256) (19/32)
  exact sign284

def polynomial285 : Quartic := ⟨4813198401900117945712367589637, 565831069524674424329929512560000, 265616185618105731471657248539274, -701453998278274424329929512560000, -495175801618099882054287632410363⟩

theorem sign285 : polynomial285.BernsteinNonnegCheck (91/256) (31/64) := by
  norm_num [polynomial285, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry285 : CachedQuarticSign :=
  ⟨polynomial285, (91/256), (31/64),
    false, .leaf⟩

theorem entry285_checked : entry285.Check := by
  change polynomial285.BernsteinNonnegCheck (91/256) (31/64)
  exact sign285

def polynomial286 : Quartic := ⟨493442080781194618723139922297580669204972162660, 1339407949798926725582102534969872936127254640837, -1702850785963037239198835920000000000000000000000, -664780445031552852285880585030127063872745359163, 141138762295319091000477677702419330795027837340⟩

theorem sign286 : polynomial286.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial286, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry286 : CachedQuarticSign :=
  ⟨polynomial286, (101/256), (19/32),
    false, .leaf⟩

theorem entry286_checked : entry286.Check := by
  change polynomial286.BernsteinNonnegCheck (101/256) (19/32)
  exact sign286

def polynomial287 : Quartic := ⟨49429601949434646014996585543063841584301227799629, -43340641487089256920596376431200000000000000000000, -124074890248957143856375790888136158415698772200371, 0, 0⟩

theorem sign287 : polynomial287.BernsteinNonnegCheck (21/64) (61/128) := by
  norm_num [polynomial287, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry287 : CachedQuarticSign :=
  ⟨polynomial287, (21/64), (61/128),
    false, .leaf⟩

theorem entry287_checked : entry287.Check := by
  change polynomial287.BernsteinNonnegCheck (21/64) (61/128)
  exact sign287

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk23
