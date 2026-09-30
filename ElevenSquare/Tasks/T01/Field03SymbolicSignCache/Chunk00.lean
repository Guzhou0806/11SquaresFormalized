import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk00
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_000 : Quartic :=
  ⟨(-1012053897491370212577100413743332487866629459 : ℚ), (-180482734824181333655816557894818495831258918 : ℚ), (3481379326096886700235600000000000000000000000 : ℚ), (-84252161798060775137416557894818495831258918 : ℚ), (-1276788793816602340340899586256667512133370541 : ℚ)⟩

theorem sign_000_00 :
    polynomial_000.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_000, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_000_00

def entry_000_00 : CachedQuarticSign :=
  ⟨polynomial_000, (2847/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_000_00_checked : entry_000_00.Check := by
  change polynomial_000.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ)
  exact sign_000_00

def polynomial_001 : Quartic :=
  ⟨(-1156636346031939848234 : ℚ), (9813971168888210531181 : ℚ), (2313272692063879696468 : ℚ), (-9813971168888210531181 : ℚ), (-1156636346031939848234 : ℚ)⟩

theorem sign_001_00 :
    polynomial_001.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_001, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_001_00

def entry_001_00 : CachedQuarticSign :=
  ⟨polynomial_001, (247/512 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_001_00_checked : entry_001_00.Check := by
  change polynomial_001.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ)
  exact sign_001_00

def polynomial_002 : Quartic :=
  ⟨(-11655 : ℚ), (7604 : ℚ), (11655 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_002_00 :
    polynomial_002.BernsteinNonnegCheck (2973/4096 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_002, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_002_00

def entry_002_00 : CachedQuarticSign :=
  ⟨polynomial_002, (2973/4096 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_002_00_checked : entry_002_00.Check := by
  change polynomial_002.BernsteinNonnegCheck (2973/4096 : ℚ) (4069/4096 : ℚ)
  exact sign_002_00

def polynomial_003 : Quartic :=
  ⟨(-1209135231031939848234 : ℚ), (10052727648888210531181 : ℚ), (2418270462063879696468 : ℚ), (-10052727648888210531181 : ℚ), (-1209135231031939848234 : ℚ)⟩

theorem sign_003_00 :
    polynomial_003.BernsteinNonnegCheck (1795/4096 : ℚ) (1001/2048 : ℚ) := by
  norm_num [polynomial_003, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_003_00

def entry_003_00 : CachedQuarticSign :=
  ⟨polynomial_003, (1795/4096 : ℚ), (1001/2048 : ℚ),
    false, .leaf⟩

theorem entry_003_00_checked : entry_003_00.Check := by
  change polynomial_003.BernsteinNonnegCheck (1795/4096 : ℚ) (1001/2048 : ℚ)
  exact sign_003_00

def polynomial_004 : Quartic :=
  ⟨(-122399 : ℚ), (348870 : ℚ), (122399 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_004_00 :
    polynomial_004.BernsteinPosCheck (647/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_004, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_004_00

def entry_004_00 : CachedQuarticSign :=
  ⟨polynomial_004, (647/2048 : ℚ), (4069/4096 : ℚ),
    true, .leaf⟩

theorem entry_004_00_checked : entry_004_00.Check := by
  change polynomial_004.BernsteinPosCheck (647/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_004_00

def polynomial_005 : Quartic :=
  ⟨(-1267 : ℚ), (356614 : ℚ), (1267 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_005_00 :
    polynomial_005.BernsteinNonnegCheck (131/512 : ℚ) (2895/4096 : ℚ) := by
  norm_num [polynomial_005, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_005_00

def entry_005_00 : CachedQuarticSign :=
  ⟨polynomial_005, (131/512 : ℚ), (2895/4096 : ℚ),
    false, .leaf⟩

theorem entry_005_00_checked : entry_005_00.Check := by
  change polynomial_005.BernsteinNonnegCheck (131/512 : ℚ) (2895/4096 : ℚ)
  exact sign_005_00

def polynomial_006 : Quartic :=
  ⟨(-12692548053943458341552815769500177 : ℚ), (26194542122446661461986115717852819 : ℚ), (-17127689695382290202652000473754976 : ℚ), (32850016962753338538013884282147181 : ℚ), (2306381961456541658447184230499823 : ℚ)⟩

theorem sign_006_00 :
    polynomial_006.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_006, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_006_00

def entry_006_00 : CachedQuarticSign :=
  ⟨polynomial_006, (65/128 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_006_00_checked : entry_006_00.Check := by
  change polynomial_006.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ)
  exact sign_006_00

def polynomial_007 : Quartic :=
  ⟨(-12935134076574315457401613507331621804142743 : ℚ), (73826582788821256944202331505864605830061486 : ℚ), (-28930558890820348587600000000000000000000000 : ℚ), (-67331961514750924599797668494135394169938514 : ℚ), (-18454106666737010899798386492668378195857257 : ℚ)⟩

theorem sign_007_00 :
    polynomial_007.BernsteinNonnegCheck (203/1024 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_007, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_007_00

def entry_007_00 : CachedQuarticSign :=
  ⟨polynomial_007, (203/1024 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_007_00_checked : entry_007_00.Check := by
  change polynomial_007.BernsteinNonnegCheck (203/1024 : ℚ) (897/2048 : ℚ)
  exact sign_007_00

def polynomial_008 : Quartic :=
  ⟨(-1308343489907752461082450841185562454820107 : ℚ), (35123186072285414563989694544862106825630614 : ℚ), (-41435640376904494267600000000000000000000000 : ℚ), (-90760701408631205020010305455137893174369386 : ℚ), (25216032342955284703882450841185562454820107 : ℚ)⟩

theorem sign_008_00 :
    polynomial_008.BernsteinNonnegCheck (161/4096 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_008, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_008_00

def entry_008_00 : CachedQuarticSign :=
  ⟨polynomial_008, (161/4096 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_008_00_checked : entry_008_00.Check := by
  change polynomial_008.BernsteinNonnegCheck (161/4096 : ℚ) (1293/4096 : ℚ)
  exact sign_008_00

def polynomial_009 : Quartic :=
  ⟨(-134630225510508626423414178129466979 : ℚ), (15728349171881346875000000000000000000 : ℚ), (4595184042987035872153171643741066042 : ℚ), (15728349171881346875000000000000000000 : ℚ), (4729814268497544498576585821870533021 : ℚ)⟩

theorem sign_009_00 :
    polynomial_009.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_009, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_009_00

def entry_009_00 : CachedQuarticSign :=
  ⟨polynomial_009, (619/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_009_00_checked : entry_009_00.Check := by
  change polynomial_009.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ)
  exact sign_009_00

def polynomial_010 : Quartic :=
  ⟨(-13772779256285876453001613507331621804142743 : ℚ), (2017969710789677287402331505864605830061486 : ℚ), (108094013200837733195600000000000000000000000 : ℚ), (4476651563280655057002331505864605830061486 : ℚ), (-19291751846448571895398386492668378195857257 : ℚ)⟩

theorem sign_010_00 :
    polynomial_010.BernsteinNonnegCheck (1795/4096 : ℚ) (751/1024 : ℚ) := by
  norm_num [polynomial_010, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_010_00

def entry_010_00 : CachedQuarticSign :=
  ⟨polynomial_010, (1795/4096 : ℚ), (751/1024 : ℚ),
    false, .leaf⟩

theorem entry_010_00_checked : entry_010_00.Check := by
  change polynomial_010.BernsteinNonnegCheck (1795/4096 : ℚ) (751/1024 : ℚ)
  exact sign_010_00

def polynomial_011 : Quartic :=
  ⟨(-137878715906385867760000157984026323831 : ℚ), (249380194039155529120359048016548605056 : ℚ), (126497231112539902169810742082511153098 : ℚ), (6870930995841270879640951983451394944 : ℚ), (999702349696532239999842015973676169 : ℚ)⟩

theorem sign_011_00 :
    polynomial_011.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_011, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_011_00

def entry_011_00 : CachedQuarticSign :=
  ⟨polynomial_011, (1923/2048 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_011_00_checked : entry_011_00.Check := by
  change polynomial_011.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_011_00

def polynomial_012 : Quartic :=
  ⟨(-1439730375619599718344564046872628540385137957 : ℚ), (-3935002581154377787497881747285121610283724086 : ℚ), (9091463900013419258443600000000000000000000000 : ℚ), (-399687423953121518590681747285121610283724086 : ℚ), (-356057873126936744834235953127371459614862043 : ℚ)⟩

theorem sign_012_00 :
    polynomial_012.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_012, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_012_00

def entry_012_00 : CachedQuarticSign :=
  ⟨polynomial_012, (2847/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_012_00_checked : entry_012_00.Check := by
  change polynomial_012.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ)
  exact sign_012_00

def polynomial_013 : Quartic :=
  ⟨(-1475363495729835095343080671248016660681969 : ℚ), (297884765861493643343262302531474445202509154 : ℚ), (132443178007088327464000000000000000000000000 : ℚ), (-332110118205889495307137697468525554797490846 : ℚ), (53855547656242972118543080671248016660681969 : ℚ)⟩

theorem sign_013_00 :
    polynomial_013.BernsteinNonnegCheck (619/4096 : ℚ) (1119/2048 : ℚ) := by
  norm_num [polynomial_013, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_013_00

def entry_013_00 : CachedQuarticSign :=
  ⟨polynomial_013, (619/4096 : ℚ), (1119/2048 : ℚ),
    false, .leaf⟩

theorem entry_013_00_checked : entry_013_00.Check := by
  change polynomial_013.BernsteinNonnegCheck (619/4096 : ℚ) (1119/2048 : ℚ)
  exact sign_013_00

def polynomial_014 : Quartic :=
  ⟨(-1513637996613068348237353131105991371815471 : ℚ), (539324237880016829522136945695655519722314718 : ℚ), (-458599242649344257187800000000000000000000000 : ℚ), (-584373479052050172603463054304344480277685282 : ℚ), (678195033552431130205237353131105991371815471 : ℚ)⟩

theorem sign_014_00 :
    polynomial_014.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_014, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_014_00

def entry_014_00 : CachedQuarticSign :=
  ⟨polynomial_014, (619/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_014_00_checked : entry_014_00.Check := by
  change polynomial_014.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ)
  exact sign_014_00

def polynomial_015 : Quartic :=
  ⟨(-15147215684368099837798382751 : ℚ), (203706933877059785465430255682 : ℚ), (30294431368736199675596765502 : ℚ), (-203706933877059785465430255682 : ℚ), (-15147215684368099837798382751 : ℚ)⟩

theorem sign_015_00 :
    polynomial_015.BernsteinNonnegCheck (1387/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_015, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_015_00

def entry_015_00 : CachedQuarticSign :=
  ⟨polynomial_015, (1387/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_015_00_checked : entry_015_00.Check := by
  change polynomial_015.BernsteinNonnegCheck (1387/4096 : ℚ) (897/2048 : ℚ)
  exact sign_015_00

def cache : List CachedQuarticSign :=
  [entry_000_00, entry_001_00, entry_002_00, entry_003_00, entry_004_00, entry_005_00, entry_006_00, entry_007_00, entry_008_00, entry_009_00, entry_010_00, entry_011_00, entry_012_00, entry_013_00, entry_014_00, entry_015_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_000_00.Check ∧ entry_001_00.Check ∧ entry_002_00.Check ∧ entry_003_00.Check ∧ entry_004_00.Check ∧ entry_005_00.Check ∧ entry_006_00.Check ∧ entry_007_00.Check ∧ entry_008_00.Check ∧ entry_009_00.Check ∧ entry_010_00.Check ∧ entry_011_00.Check ∧ entry_012_00.Check ∧ entry_013_00.Check ∧ entry_014_00.Check ∧ entry_015_00.Check ∧ True
  exact ⟨entry_000_00_checked, entry_001_00_checked, entry_002_00_checked, entry_003_00_checked, entry_004_00_checked, entry_005_00_checked, entry_006_00_checked, entry_007_00_checked, entry_008_00_checked, entry_009_00_checked, entry_010_00_checked, entry_011_00_checked, entry_012_00_checked, entry_013_00_checked, entry_014_00_checked, entry_015_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk00
