import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk03
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_048 : Quartic :=
  ⟨(-33361681455742302757427493233 : ℚ), (3823232441309983647087685653406 : ℚ), (66723362911484605514854986466 : ℚ), (-3823232441309983647087685653406 : ℚ), (-33361681455742302757427493233 : ℚ)⟩

theorem sign_048_00 :
    polynomial_048.BernsteinNonnegCheck (619/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_048, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_048_00

def entry_048_00 : CachedQuarticSign :=
  ⟨polynomial_048, (619/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_048_00_checked : entry_048_00.Check := by
  change polynomial_048.BernsteinNonnegCheck (619/4096 : ℚ) (897/2048 : ℚ)
  exact sign_048_00

def polynomial_049 : Quartic :=
  ⟨(-338306158004508657681859278870373641 : ℚ), (-143564766194043775315094786942770747282 : ℚ), (395133494665539600000000000000000000000 : ℚ), (-122058839655459775315094786942770747282 : ℚ), (-138541500910036691342318140721129626359 : ℚ)⟩

theorem sign_049_00 :
    polynomial_049.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_049, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_049_00

def entry_049_00 : CachedQuarticSign :=
  ⟨polynomial_049, (633/1024 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_049_00_checked : entry_049_00.Check := by
  change polynomial_049.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ)
  exact sign_049_00

def polynomial_050 : Quartic :=
  ⟨(-3526763533062006619361527423 : ℚ), (7237794094938579563850134945154 : ℚ), (7053527066124013238723054846 : ℚ), (-7237794094938579563850134945154 : ℚ), (-3526763533062006619361527423 : ℚ)⟩

theorem sign_050_00 :
    polynomial_050.BernsteinNonnegCheck (161/4096 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_050, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_050_00

def entry_050_00 : CachedQuarticSign :=
  ⟨polynomial_050, (161/4096 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_050_00_checked : entry_050_00.Check := by
  change polynomial_050.BernsteinNonnegCheck (161/4096 : ℚ) (4069/4096 : ℚ)
  exact sign_050_00

def polynomial_051 : Quartic :=
  ⟨(-365148648028236481014653616072192258460577077 : ℚ), (-540861065818088403067059121491486794772845846 : ℚ), (4557595212307370046185200000000000000000000000 : ℚ), (1134316352166553135220940878508513205227154154 : ℚ), (-513512469781804221617746383927807741539422923 : ℚ)⟩

theorem sign_051_00 :
    polynomial_051.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ) := by
  norm_num [polynomial_051, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_051_00

def entry_051_00 : CachedQuarticSign :=
  ⟨polynomial_051, (633/1024 : ℚ), (1423/2048 : ℚ),
    false, .leaf⟩

theorem entry_051_00_checked : entry_051_00.Check := by
  change polynomial_051.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ)
  exact sign_051_00

def polynomial_052 : Quartic :=
  ⟨(-379723517884126546287334976316955437 : ℚ), (190430776664672282146458460448006976 : ℚ), (-9220167371600000000000000000000000 : ℚ), (-203890251335327717853541539551993024 : ℚ), (783256642512526546287334976316955437 : ℚ)⟩

theorem sign_052_00 :
    polynomial_052.BernsteinNonnegCheck (1663/2048 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_052, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_052_00

def entry_052_00 : CachedQuarticSign :=
  ⟨polynomial_052, (1663/2048 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_052_00_checked : entry_052_00.Check := by
  change polynomial_052.BernsteinNonnegCheck (1663/2048 : ℚ) (3863/4096 : ℚ)
  exact sign_052_00

def polynomial_053 : Quartic :=
  ⟨(-3801313024026937993380638472577 : ℚ), (14792220188781420436149865054846 : ℚ), (-5450331310026124013238723054846 : ℚ), (487627011218579563850134945154 : ℚ), (-3801389424026937993380638472577 : ℚ)⟩

theorem sign_053_00 :
    polynomial_053.BernsteinNonnegCheck (633/1024 : ℚ) (3355/4096 : ℚ) := by
  norm_num [polynomial_053, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_053_00

def entry_053_00 : CachedQuarticSign :=
  ⟨polynomial_053, (633/1024 : ℚ), (3355/4096 : ℚ),
    false, .leaf⟩

theorem entry_053_00_checked : entry_053_00.Check := by
  change polynomial_053.BernsteinNonnegCheck (633/1024 : ℚ) (3355/4096 : ℚ)
  exact sign_053_00

def polynomial_054 : Quartic :=
  ⟨(-3801313024026937993380638472577 : ℚ), (14792220188781420436149865054846 : ℚ), (-7642700820426124013238723054846 : ℚ), (487627011218579563850134945154 : ℚ), (-3801389424026937993380638472577 : ℚ)⟩

theorem sign_054_00 :
    polynomial_054.BernsteinNonnegCheck (3301/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_054, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_054_00

def entry_054_00 : CachedQuarticSign :=
  ⟨polynomial_054, (3301/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_054_00_checked : entry_054_00.Check := by
  change polynomial_054.BernsteinNonnegCheck (3301/4096 : ℚ) (127/128 : ℚ)
  exact sign_054_00

def polynomial_055 : Quartic :=
  ⟨(-3888311437662106993164318939414168315735943 : ℚ), (-6349739744385215902109636297466157091525310 : ℚ), (29749336639636152121650000000000000000000000 : ℚ), (-1345802628974266499559636297466157091525310 : ℚ), (-5737032176913187050835681060585831684264057 : ℚ)⟩

theorem sign_055_00 :
    polynomial_055.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_055, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_055_00

def entry_055_00 : CachedQuarticSign :=
  ⟨polynomial_055, (65/128 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_055_00_checked : entry_055_00.Check := by
  change polynomial_055.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ)
  exact sign_055_00

def polynomial_056 : Quartic :=
  ⟨(-39758520597821173174101913 : ℚ), (472614771809171936697569104 : ℚ), (79517041195642346348203826 : ℚ), (-472614771809171936697569104 : ℚ), (-39758520597821173174101913 : ℚ)⟩

theorem sign_056_00 :
    polynomial_056.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_056, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_056_00

def entry_056_00 : CachedQuarticSign :=
  ⟨polynomial_056, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_056_00_checked : entry_056_00.Check := by
  change polynomial_056.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_056_00

def polynomial_057 : Quartic :=
  ⟨(-4030919308871668604453712666171305451 : ℚ), (19694365130032035004461221728323671860 : ℚ), (54885584708837928691458236212615971306 : ℚ), (-147819927647530435004461221728323671860 : ℚ), (-73470128436912868604453712666171305451 : ℚ)⟩

theorem sign_057_00 :
    polynomial_057.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_057, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_057_00

def entry_057_00 : CachedQuarticSign :=
  ⟨polynomial_057, (677/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_057_00_checked : entry_057_00.Check := by
  change polynomial_057.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ)
  exact sign_057_00

def polynomial_058 : Quartic :=
  ⟨(-4042562828690300590357230511808706203685069 : ℚ), (3295488708309039245481262758386750916996582 : ℚ), (18311063378876014636720000000000000000000000 : ℚ), (-4202203372326147235798737241613249083003418 : ℚ), (-5293330520947454626042769488191293796314931 : ℚ)⟩

theorem sign_058_00 :
    polynomial_058.BernsteinNonnegCheck (3005/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_058, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_058_00

def entry_058_00 : CachedQuarticSign :=
  ⟨polynomial_058, (3005/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_058_00_checked : entry_058_00.Check := by
  change polynomial_058.BernsteinNonnegCheck (3005/4096 : ℚ) (127/128 : ℚ)
  exact sign_058_00

def polynomial_059 : Quartic :=
  ⟨(-409284477902837879794082390969147761 : ℚ), (1062777506305188742415154027016581943 : ℚ), (-50166606359111768489604050995305960 : ℚ), (1000947678365611257584845972983418057 : ℚ), (576498376045762120205917609030852239 : ℚ)⟩

theorem sign_059_00 :
    polynomial_059.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_059, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_059_00

def entry_059_00 : CachedQuarticSign :=
  ⟨polynomial_059, (717/2048 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_059_00_checked : entry_059_00.Check := by
  change polynomial_059.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ)
  exact sign_059_00

def polynomial_060 : Quartic :=
  ⟨(-411749998182749256120937494264017440 : ℚ), (851416423946712186465479254258141981 : ℚ), (353150776132713544509467712099463678 : ℚ), (1212308760724087813534520745741858019 : ℚ), (574032855765850743879062505735982560 : ℚ)⟩

theorem sign_060_00 :
    polynomial_060.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_060, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_060_00

def entry_060_00 : CachedQuarticSign :=
  ⟨polynomial_060, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_060_00_checked : entry_060_00.Check := by
  change polynomial_060.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_060_00

def polynomial_061 : Quartic :=
  ⟨(-427967026031939848234 : ℚ), (978673938888210531181 : ℚ), (-4590938787936120303532 : ℚ), (19021126061111789468819 : ℚ), (-10427867026031939848234 : ℚ)⟩

theorem sign_061_00 :
    polynomial_061.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_061, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_061_00

def entry_061_00 : CachedQuarticSign :=
  ⟨polynomial_061, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_061_00_checked : entry_061_00.Check := by
  change polynomial_061.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_061_00

def polynomial_062 : Quartic :=
  ⟨(-431815252999590859529292616720357731728627329 : ℚ), (820550260550948933573006987591047227173750914 : ℚ), (1711857553341218479159600000000000000000000000 : ℚ), (-712023609989215894078193012408952772826249086 : ℚ), (-607266433148966442045507383279642268271372671 : ℚ)⟩

theorem sign_062_00 :
    polynomial_062.BernsteinNonnegCheck (1387/4096 : ℚ) (1423/2048 : ℚ) := by
  norm_num [polynomial_062, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_062_00

def entry_062_00 : CachedQuarticSign :=
  ⟨polynomial_062, (1387/4096 : ℚ), (1423/2048 : ℚ),
    false, .leaf⟩

theorem entry_062_00_checked : entry_062_00.Check := by
  change polynomial_062.BernsteinNonnegCheck (1387/4096 : ℚ) (1423/2048 : ℚ)
  exact sign_062_00

def polynomial_063 : Quartic :=
  ⟨(-44025741455410491493351100747845831692719143 : ℚ), (1075284985179745965981380802779893898388805838 : ℚ), (-2202078472558684360309200000000000000000000000 : ℚ), (-1172110448684388038269819197220106101611194162 : ℚ), (112508545307050769273751100747845831692719143 : ℚ)⟩

theorem sign_063_00 :
    polynomial_063.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_063, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_063_00

def entry_063_00 : CachedQuarticSign :=
  ⟨polynomial_063, (619/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_063_00_checked : entry_063_00.Check := by
  change polynomial_063.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ)
  exact sign_063_00

def cache : List CachedQuarticSign :=
  [entry_048_00, entry_049_00, entry_050_00, entry_051_00, entry_052_00, entry_053_00, entry_054_00, entry_055_00, entry_056_00, entry_057_00, entry_058_00, entry_059_00, entry_060_00, entry_061_00, entry_062_00, entry_063_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_048_00.Check ∧ entry_049_00.Check ∧ entry_050_00.Check ∧ entry_051_00.Check ∧ entry_052_00.Check ∧ entry_053_00.Check ∧ entry_054_00.Check ∧ entry_055_00.Check ∧ entry_056_00.Check ∧ entry_057_00.Check ∧ entry_058_00.Check ∧ entry_059_00.Check ∧ entry_060_00.Check ∧ entry_061_00.Check ∧ entry_062_00.Check ∧ entry_063_00.Check ∧ True
  exact ⟨entry_048_00_checked, entry_049_00_checked, entry_050_00_checked, entry_051_00_checked, entry_052_00_checked, entry_053_00_checked, entry_054_00_checked, entry_055_00_checked, entry_056_00_checked, entry_057_00_checked, entry_058_00_checked, entry_059_00_checked, entry_060_00_checked, entry_061_00_checked, entry_062_00_checked, entry_063_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk03
