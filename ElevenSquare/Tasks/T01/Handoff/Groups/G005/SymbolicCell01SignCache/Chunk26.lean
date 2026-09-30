import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk26
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial312 : Quartic := ⟨5903842499415163874274724603922323204209075849407117, 1257836753124332833959524819191560000000000000000000000, 329182246297007224071270219526602323204209075849407117, 0, 0⟩

theorem sign312 : polynomial312.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial312, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry312 : CachedQuarticSign :=
  ⟨polynomial312, 0, 1,
    false, .leaf⟩

theorem entry312_checked : entry312.Check := by
  change polynomial312.BernsteinNonnegCheck 0 1
  exact sign312

def polynomial313 : Quartic := ⟨612851173517544747124565773502270175517521379, -3557931221003218243783210838906568494377542000, 3168300567555059592264140000000000000000000000, -621015627535421325246290838906568494377542000, 822173727983289170121374226497729824482478621⟩

theorem sign313 : polynomial313.BernsteinNonnegCheck (57/64) 1 := by
  norm_num [polynomial313, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry313 : CachedQuarticSign :=
  ⟨polynomial313, (57/64), 1,
    false, .leaf⟩

theorem entry313_checked : entry313.Check := by
  change polynomial313.BernsteinNonnegCheck (57/64) 1
  exact sign313

def polynomial314 : Quartic := ⟨616342827251399678148638271566872464040755937, -5745510676934779735884574541502547753687131768, -1014983571077282243031320000000000000000000000, 4354166343983796838081025458497452246312868232, 121149826371164840207881728433127535959244063⟩

theorem sign314 : polynomial314.BernsteinNonnegCheck (5/256) (3/32) := by
  norm_num [polynomial314, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry314 : CachedQuarticSign :=
  ⟨polynomial314, (5/256), (3/32),
    false, .leaf⟩

theorem entry314_checked : entry314.Check := by
  change polynomial314.BernsteinNonnegCheck (5/256) (3/32)
  exact sign314

def polynomial315 : Quartic := ⟨61900941512221654387934255614827500000, 1158257905178714629369012388031442496953, -2350995427628888040000000000000000000000, -138843019092397330630987611968557503047, 1154131175787778345612065744385172500000⟩

theorem sign315 : polynomial315.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial315, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry315 : CachedQuarticSign :=
  ⟨polynomial315, 0, (1/64),
    false, .leaf⟩

theorem entry315_checked : entry315.Check := by
  change polynomial315.BernsteinNonnegCheck 0 (1/64)
  exact sign315

def polynomial316 : Quartic := ⟨619098260366058552977206832255346155, -684765833111562277025043294486413074, 2739768800867960000000000000000000000, -3401752293111562277025043294486413074, 739392920501901447022793167744653845⟩

theorem sign316 : polynomial316.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial316, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry316 : CachedQuarticSign :=
  ⟨polynomial316, 0, 1,
    false, .leaf⟩

theorem entry316_checked : entry316.Check := by
  change polynomial316.BernsteinNonnegCheck 0 1
  exact sign316

def polynomial317 : Quartic := ⟨6195248201501459902548995977031608719, 8777613229658430160000000000000000000000, -9223727080036922300097451004022968391281, 0, 0⟩

theorem sign317 : polynomial317.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial317, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry317 : CachedQuarticSign :=
  ⟨polynomial317, (11/16), (27/32),
    false, .leaf⟩

theorem entry317_checked : entry317.Check := by
  change polynomial317.BernsteinNonnegCheck (11/16) (27/32)
  exact sign317

def polynomial318 : Quartic := ⟨628853101568522819562803606, 37796183222991127560412975989, 380741529796862954360874392788, -37796183222991127560412975989, -381370382898431477180437196394⟩

theorem sign318 : polynomial318.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial318, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry318 : CachedQuarticSign :=
  ⟨polynomial318, 0, 1,
    false, .leaf⟩

theorem entry318_checked : entry318.Check := by
  change polynomial318.BernsteinNonnegCheck 0 1
  exact sign318

def polynomial319 : Quartic := ⟨6512744675524564449405932604259490856700073544427087, 229004657674362583238267477655340000000000000000000000, 53525006962678353523929577905739490856700073544427087, 0, 0⟩

theorem sign319 : polynomial319.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial319, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry319 : CachedQuarticSign :=
  ⟨polynomial319, 0, 1,
    false, .leaf⟩

theorem entry319_checked : entry319.Check := by
  change polynomial319.BernsteinNonnegCheck 0 1
  exact sign319

def polynomial320 : Quartic := ⟨67758754348353598363563878736555617078190325, -3742636825742441103563022388573656313192449, -52380508727819191907660000000000000000000000, -200204729137734367178763022388573656313192449, 254494353024324991271736121263444382921809675⟩

theorem sign320 : polynomial320.BernsteinNonnegCheck (101/256) (61/128) := by
  norm_num [polynomial320, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry320 : CachedQuarticSign :=
  ⟨polynomial320, (101/256), (61/128),
    false, .leaf⟩

theorem entry320_checked : entry320.Check := by
  change polynomial320.BernsteinNonnegCheck (101/256) (61/128)
  exact sign320

def polynomial321 : Quartic := ⟨6783599306109541840773365858225420096750709, -55326604001104113467252441035729590137501418, -937847295161608770099020000000000000000000000, -2322417761362219248470772441035729590137501418, 601219691814026949857726634141774579903249291⟩

theorem sign321 : polynomial321.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial321, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry321 : CachedQuarticSign :=
  ⟨polynomial321, 0, (1/64),
    false, .leaf⟩

theorem entry321_checked : entry321.Check := by
  change polynomial321.BernsteinNonnegCheck 0 (1/64)
  exact sign321

def polynomial322 : Quartic := ⟨689925635803105602122047388974975438222920445, -180659757747275475645983419287382685144883302, -4802056658933740687466360000000000000000000000, 29730613956159514314096580712617314855116698, 1014071470942131725344312611025024561777079555⟩

theorem sign322 : polynomial322.BernsteinNonnegCheck (7/64) (1/4) := by
  norm_num [polynomial322, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry322 : CachedQuarticSign :=
  ⟨polynomial322, (7/64), (1/4),
    false, .leaf⟩

theorem entry322_checked : entry322.Check := by
  change polynomial322.BernsteinNonnegCheck (7/64) (1/4)
  exact sign322

def polynomial323 : Quartic := ⟨700333333, -1910000000, -700333333, 0, 0⟩

theorem sign323 : polynomial323.BernsteinNonnegCheck 0 (5/16) := by
  norm_num [polynomial323, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry323 : CachedQuarticSign :=
  ⟨polynomial323, 0, (5/16),
    false, .leaf⟩

theorem entry323_checked : entry323.Check := by
  change polynomial323.BernsteinNonnegCheck 0 (5/16)
  exact sign323

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk26
