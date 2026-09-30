import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk05
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_080 : Quartic :=
  ⟨(-60219542427344799593669881611224274370540347 : ℚ), (411711877270364923186659799187655819537436682 : ℚ), (8657339964641529923440000000000000000000000 : ℚ), (-621086150967452654617180200812344180462563318 : ℚ), (-92597051399918903044170118388775725629459653 : ℚ)⟩

theorem sign_080_00 :
    polynomial_080.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ) := by
  norm_num [polynomial_080, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_080_00

def entry_080_00 : CachedQuarticSign :=
  ⟨polynomial_080, (633/1024 : ℚ), (1423/2048 : ℚ),
    false, .leaf⟩

theorem entry_080_00_checked : entry_080_00.Check := by
  change polynomial_080.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ)
  exact sign_080_00

def polynomial_081 : Quartic :=
  ⟨(-612840493420792847911315012022274726943 : ℚ), (4032564714287097251139688531209136360638 : ℚ), (-2781174956460812400000000000000000000000 : ℚ), (-6511051079860589148860311468790863639362 : ℚ), (3394040356335543647911315012022274726943 : ℚ)⟩

theorem sign_081_00 :
    polynomial_081.BernsteinNonnegCheck (1795/4096 : ℚ) (1119/2048 : ℚ) := by
  norm_num [polynomial_081, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_081_00

def entry_081_00 : CachedQuarticSign :=
  ⟨polynomial_081, (1795/4096 : ℚ), (1119/2048 : ℚ),
    false, .leaf⟩

theorem entry_081_00_checked : entry_081_00.Check := by
  change polynomial_081.BernsteinNonnegCheck (1795/4096 : ℚ) (1119/2048 : ℚ)
  exact sign_081_00

def polynomial_082 : Quartic :=
  ⟨(-62664581954692517553616727232877 : ℚ), (340498731114597215234118613000000 : ℚ), (-298365323081446783543049274065754 : ℚ), (-23643468346597215234118613000000 : ℚ), (-8884057586692517553616727232877 : ℚ)⟩

theorem sign_082_00 :
    polynomial_082.BernsteinNonnegCheck (1795/4096 : ℚ) (1119/2048 : ℚ) := by
  norm_num [polynomial_082, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_082_00

def entry_082_00 : CachedQuarticSign :=
  ⟨polynomial_082, (1795/4096 : ℚ), (1119/2048 : ℚ),
    false, .leaf⟩

theorem entry_082_00_checked : entry_082_00.Check := by
  change polynomial_082.BernsteinNonnegCheck (1795/4096 : ℚ) (1119/2048 : ℚ)
  exact sign_082_00

def polynomial_083 : Quartic :=
  ⟨(-6667299230112444886493554768884111249 : ℚ), (-579539978707850322124873846142929894306 : ℚ), (4649152775227327800000000000000000000000 : ℚ), (-3360727388395631922124873846142929894306 : ℚ), (-615987822616402955113506445231115888751 : ℚ)⟩

theorem sign_083_00 :
    polynomial_083.BernsteinNonnegCheck (619/4096 : ℚ) (811/4096 : ℚ) := by
  norm_num [polynomial_083, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_083_00

def entry_083_00 : CachedQuarticSign :=
  ⟨polynomial_083, (619/4096 : ℚ), (811/4096 : ℚ),
    false, .leaf⟩

theorem entry_083_00_checked : entry_083_00.Check := by
  change polynomial_083.BernsteinNonnegCheck (619/4096 : ℚ) (811/4096 : ℚ)
  exact sign_083_00

def polynomial_084 : Quartic :=
  ⟨(-68446410830503389361031151265737222601254577 : ℚ), (-95362408075260402434286161342496033321363938 : ℚ), (475989386234178433946400000000000000000000000 : ℚ), (-15299414228685211993486161342496033321363938 : ℚ), (-85559087002701315342968848734262777398745423 : ℚ)⟩

theorem sign_084_00 :
    polynomial_084.BernsteinNonnegCheck (633/1024 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_084, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_084_00

def entry_084_00 : CachedQuarticSign :=
  ⟨polynomial_084, (633/1024 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_084_00_checked : entry_084_00.Check := by
  change polynomial_084.BernsteinNonnegCheck (633/1024 : ℚ) (4069/4096 : ℚ)
  exact sign_084_00

def polynomial_085 : Quartic :=
  ⟨(-706880392718433694677391631514372073 : ℚ), (3558783576412818271221689863511332904 : ℚ), (-2829850234810565414262023368781233130 : ℚ), (-532815816978418271221689863511332904 : ℚ), (-193276385004033694677391631514372073 : ℚ)⟩

theorem sign_085_00 :
    polynomial_085.BernsteinNonnegCheck (647/2048 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_085, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_085_00

def entry_085_00 : CachedQuarticSign :=
  ⟨polynomial_085, (647/2048 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_085_00_checked : entry_085_00.Check := by
  change polynomial_085.BernsteinNonnegCheck (647/2048 : ℚ) (897/2048 : ℚ)
  exact sign_085_00

def polynomial_086 : Quartic :=
  ⟨(-74717108559460416842146032657025582 : ℚ), (4210918487193600110117921723425371655 : ℚ), (-5530477932486542930019389362989265218 : ℚ), (476696938622799889882078276574628345 : ℚ), (-416628920186460416842146032657025582 : ℚ)⟩

theorem sign_086_00 :
    polynomial_086.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_086, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_086_00

def entry_086_00 : CachedQuarticSign :=
  ⟨polynomial_086, (75/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_086_00_checked : entry_086_00.Check := by
  change polynomial_086.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ)
  exact sign_086_00

def polynomial_087 : Quartic :=
  ⟨(-807952692921296805250055357695099011 : ℚ), (2561933055219537656736658259231177922 : ℚ), (-2567949999865200000000000000000000000 : ℚ), (-113969304780462343263341740768822078 : ℚ), (3375878093056096805250055357695099011 : ℚ)⟩

theorem sign_087_00 :
    polynomial_087.BernsteinNonnegCheck (2847/4096 : ℚ) (751/1024 : ℚ) := by
  norm_num [polynomial_087, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_087_00

def entry_087_00 : CachedQuarticSign :=
  ⟨polynomial_087, (2847/4096 : ℚ), (751/1024 : ℚ),
    false, .leaf⟩

theorem entry_087_00_checked : entry_087_00.Check := by
  change polynomial_087.BernsteinNonnegCheck (2847/4096 : ℚ) (751/1024 : ℚ)
  exact sign_087_00

def polynomial_088 : Quartic :=
  ⟨(-819331296383977671398641119534731231 : ℚ), (2063725184670800000000000000000000000 : ℚ), (332903115129244657202717760930537538 : ℚ), (2063725184670800000000000000000000000 : ℚ), (1152234411513222328601358880465268769 : ℚ)⟩

theorem sign_088_00 :
    polynomial_088.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ) := by
  norm_num [polynomial_088, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_088_00

def entry_088_00 : CachedQuarticSign :=
  ⟨polynomial_088, (633/1024 : ℚ), (1423/2048 : ℚ),
    false, .leaf⟩

theorem entry_088_00_checked : entry_088_00.Check := by
  change polynomial_088.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ)
  exact sign_088_00

def polynomial_089 : Quartic :=
  ⟨(-891333333 : ℚ), (891333334 : ℚ), (0 : ℚ), (891333334 : ℚ), (891333333 : ℚ)⟩

theorem sign_089_00 :
    polynomial_089.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_089, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_089_00

def entry_089_00 : CachedQuarticSign :=
  ⟨polynomial_089, (1923/2048 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_089_00_checked : entry_089_00.Check := by
  change polynomial_089.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_089_00

def polynomial_090 : Quartic :=
  ⟨(-891333333 : ℚ), (891333334 : ℚ), (891333333 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_090_00 :
    polynomial_090.BernsteinNonnegCheck (633/1024 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_090, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_090_00

def entry_090_00 : CachedQuarticSign :=
  ⟨polynomial_090, (633/1024 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_090_00_checked : entry_090_00.Check := by
  change polynomial_090.BernsteinNonnegCheck (633/1024 : ℚ) (4069/4096 : ℚ)
  exact sign_090_00

def polynomial_091 : Quartic :=
  ⟨(-950970173709728874230287839613640952243095855694489 : ℚ), (8624557030250254106135355986918750000000000000000000 : ℚ), (29499183488319583991673456267609047756904144305511 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_091_00 :
    polynomial_091.BernsteinNonnegCheck (1387/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_091, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_091_00

def entry_091_00 : CachedQuarticSign :=
  ⟨polynomial_091, (1387/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_091_00_checked : entry_091_00.Check := by
  change polynomial_091.BernsteinNonnegCheck (1387/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_091_00

def polynomial_092 : Quartic :=
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_092_00 :
    polynomial_092.BernsteinPosCheck (1/4096 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_092, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_092_00

def entry_092_00 : CachedQuarticSign :=
  ⟨polynomial_092, (1/4096 : ℚ), (4069/4096 : ℚ),
    true, .leaf⟩

theorem entry_092_00_checked : entry_092_00.Check := by
  change polynomial_092.BernsteinPosCheck (1/4096 : ℚ) (4069/4096 : ℚ)
  exact sign_092_00

def polynomial_093 : Quartic :=
  ⟨(0 : ℚ), (152570330249289781925067472577 : ℚ), (-1156403865293875986761276945154 : ℚ), (7487276869750710218074932527423 : ℚ), (0 : ℚ)⟩

theorem sign_093_00 :
    polynomial_093.BernsteinNonnegCheck (343/4096 : ℚ) (1001/2048 : ℚ) := by
  norm_num [polynomial_093, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_093_00

def entry_093_00 : CachedQuarticSign :=
  ⟨polynomial_093, (343/4096 : ℚ), (1001/2048 : ℚ),
    false, .leaf⟩

theorem entry_093_00_checked : entry_093_00.Check := by
  change polynomial_093.BernsteinNonnegCheck (343/4096 : ℚ) (1001/2048 : ℚ)
  exact sign_093_00

def polynomial_094 : Quartic :=
  ⟨(0 : ℚ), (201026552530710218074932527423 : ℚ), (-7053527066124013238723054846 : ℚ), (7438820647469289781925067472577 : ℚ), (0 : ℚ)⟩

theorem sign_094_00 :
    polynomial_094.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_094, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_094_00

def entry_094_00 : CachedQuarticSign :=
  ⟨polynomial_094, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_094_00_checked : entry_094_00.Check := by
  change polynomial_094.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_094_00

def polynomial_095 : Quartic :=
  ⟨(0 : ℚ), (243775305609289781925067472577 : ℚ), (-1076185569013875986761276945154 : ℚ), (7396071894390710218074932527423 : ℚ), (0 : ℚ)⟩

theorem sign_095_00 :
    polynomial_095.BernsteinNonnegCheck (247/512 : ℚ) (3355/4096 : ℚ) := by
  norm_num [polynomial_095, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_095_00

def entry_095_00 : CachedQuarticSign :=
  ⟨polynomial_095, (247/512 : ℚ), (3355/4096 : ℚ),
    false, .leaf⟩

theorem entry_095_00_checked : entry_095_00.Check := by
  change polynomial_095.BernsteinNonnegCheck (247/512 : ℚ) (3355/4096 : ℚ)
  exact sign_095_00

def cache : List CachedQuarticSign :=
  [entry_080_00, entry_081_00, entry_082_00, entry_083_00, entry_084_00, entry_085_00, entry_086_00, entry_087_00, entry_088_00, entry_089_00, entry_090_00, entry_091_00, entry_092_00, entry_093_00, entry_094_00, entry_095_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_080_00.Check ∧ entry_081_00.Check ∧ entry_082_00.Check ∧ entry_083_00.Check ∧ entry_084_00.Check ∧ entry_085_00.Check ∧ entry_086_00.Check ∧ entry_087_00.Check ∧ entry_088_00.Check ∧ entry_089_00.Check ∧ entry_090_00.Check ∧ entry_091_00.Check ∧ entry_092_00.Check ∧ entry_093_00.Check ∧ entry_094_00.Check ∧ entry_095_00.Check ∧ True
  exact ⟨entry_080_00_checked, entry_081_00_checked, entry_082_00_checked, entry_083_00_checked, entry_084_00_checked, entry_085_00_checked, entry_086_00_checked, entry_087_00_checked, entry_088_00_checked, entry_089_00_checked, entry_090_00_checked, entry_091_00_checked, entry_092_00_checked, entry_093_00_checked, entry_094_00_checked, entry_095_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk05
