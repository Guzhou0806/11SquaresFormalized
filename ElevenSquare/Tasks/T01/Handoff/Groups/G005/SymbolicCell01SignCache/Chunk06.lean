import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk06
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial072 : Quartic := ⟨-4093, 1069720, 4093, 0, 0⟩

theorem sign072 : polynomial072.BernsteinPosCheck (91/256) 1 := by
  norm_num [polynomial072, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry072 : CachedQuarticSign :=
  ⟨polynomial072, (91/256), 1,
    true, .leaf⟩

theorem entry072_checked : entry072.Check := by
  change polynomial072.BernsteinPosCheck (91/256) 1
  exact sign072

def polynomial073 : Quartic := ⟨-43883820512725500966050636746654533181, 227741990760680816220320754873214778660, 3795208352009348697186973700010612756406, -4119040879907337296220320754873214778660, -3935182702019397260966050636746654533181⟩

theorem sign073 : polynomial073.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial073, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry073 : CachedQuarticSign :=
  ⟨polynomial073, (101/256), (19/32),
    false, .leaf⟩

theorem entry073_checked : entry073.Check := by
  change polynomial073.BernsteinNonnegCheck (101/256) (19/32)
  exact sign073

def polynomial074 : Quartic := ⟨-43996088008877448442887960322571, 306494529063313993501885623200000, 564096462675995554267271146554858, -17222307608913993501885623200000, -328496719006477448442887960322571⟩

theorem sign074 : polynomial074.BernsteinNonnegCheck (21/64) (61/128) := by
  norm_num [polynomial074, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry074 : CachedQuarticSign :=
  ⟨polynomial074, (21/64), (61/128),
    false, .leaf⟩

theorem entry074_checked : entry074.Check := by
  change polynomial074.BernsteinNonnegCheck (21/64) (61/128)
  exact sign074

def polynomial075 : Quartic := ⟨-44310872930840401901745438186468955911522956220, -3236277116172325374422157830898863360204634217987, 11614631768056968468053596040000000000000000000000, -5903597810728437219721634550898863360204634217987, -3187700260802327263351850601813531044088477043780⟩

theorem sign075 : polynomial075.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial075, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry075 : CachedQuarticSign :=
  ⟨polynomial075, (11/16), (27/32),
    false, .leaf⟩

theorem entry075_checked : entry075.Check := by
  change polynomial075.BernsteinNonnegCheck (11/16) (27/32)
  exact sign075

def polynomial076 : Quartic := ⟨-45072604901710097432866209145747873, -282057370684669227878652692610035329, -3868970370415764656399153795916437554, 5056952320875669227878652692610035329, -368872347300930097432866209145747873⟩

theorem sign076 : polynomial076.BernsteinNonnegCheck (115/128) 1 := by
  norm_num [polynomial076, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry076 : CachedQuarticSign :=
  ⟨polynomial076, (115/128), 1,
    false, .leaf⟩

theorem entry076_checked : entry076.Check := by
  change polynomial076.BernsteinNonnegCheck (115/128) 1
  exact sign076

def polynomial077 : Quartic := ⟨-46236966230558525252082134346693000000, 141979393023617557569651038111865207829, -151452127518088012000000000000000000000, 99564215182837813569651038111865207829, 197688963504042817252082134346693000000⟩

theorem sign077 : polynomial077.BernsteinNonnegCheck (61/128) (31/64) := by
  norm_num [polynomial077, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry077 : CachedQuarticSign :=
  ⟨polynomial077, (61/128), (31/64),
    false, .leaf⟩

theorem entry077_checked : entry077.Check := by
  change polynomial077.BernsteinNonnegCheck (61/128) (31/64)
  exact sign077

def polynomial078 : Quartic := ⟨-4700634862482294157754035736710629107752558453449, 345466504237509012103603795368800000000000000000000, -246408079296160447711317193199910629107752558453449, 0, 0⟩

theorem sign078 : polynomial078.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial078, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry078 : CachedQuarticSign :=
  ⟨polynomial078, (21/64), (91/256),
    false, .leaf⟩

theorem entry078_checked : entry078.Check := by
  change polynomial078.BernsteinNonnegCheck (21/64) (91/256)
  exact sign078

def polynomial079 : Quartic := ⟨-471840355039171674175851053732654517397644675, -403551585323297603602089605407220201159489299, 2093941614015405835980700000000000000000000000, 603762446892224681165950394592779798840510701, -646359036624581841804848946267345482602355325⟩

theorem sign079 : polynomial079.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial079, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry079 : CachedQuarticSign :=
  ⟨polynomial079, (11/16), (27/32),
    false, .leaf⟩

theorem entry079_checked : entry079.Check := by
  change polynomial079.BernsteinNonnegCheck (11/16) (27/32)
  exact sign079

def polynomial080 : Quartic := ⟨-477500000, 445666667, 0, 445666667, 477500000⟩

theorem sign080 : polynomial080.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial080, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry080 : CachedQuarticSign :=
  ⟨polynomial080, (11/16), (27/32),
    false, .leaf⟩

theorem entry080_checked : entry080.Check := by
  change polynomial080.BernsteinNonnegCheck (11/16) (27/32)
  exact sign080

def polynomial081 : Quartic := ⟨-477500000, 445666667, 477500000, 0, 0⟩

theorem sign081 : polynomial081.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial081, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry081 : CachedQuarticSign :=
  ⟨polynomial081, (11/16), (27/32),
    false, .leaf⟩

theorem entry081_checked : entry081.Check := by
  change polynomial081.BernsteinNonnegCheck (11/16) (27/32)
  exact sign081

def polynomial082 : Quartic := ⟨-4811496161104264112936733442890351241007, 3273273209320029285965171090159577517986, 15082976726837601160000000000000000000000, -18154240196642743834034828909840422482014, 4811506874864139352936733442890351241007⟩

theorem sign082 : polynomial082.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial082, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry082 : CachedQuarticSign :=
  ⟨polynomial082, (27/32), 1,
    false, .leaf⟩

theorem entry082_checked : entry082.Check := by
  change polynomial082.BernsteinNonnegCheck (27/32) 1
  exact sign082

def polynomial083 : Quartic := ⟨-483069867537682985641785465198275597, 20463129565657307000000000000000000000, -21460187045217709985641785465198275597, 0, 0⟩

theorem sign083 : polynomial083.BernsteinNonnegCheck (1/16) (59/64) := by
  norm_num [polynomial083, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry083 : CachedQuarticSign :=
  ⟨polynomial083, (1/16), (59/64),
    false, .leaf⟩

theorem entry083_checked : entry083.Check := by
  change polynomial083.BernsteinNonnegCheck (1/16) (59/64)
  exact sign083

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk06
