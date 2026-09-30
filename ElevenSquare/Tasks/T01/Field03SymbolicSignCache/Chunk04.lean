import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk04
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_064 : Quartic :=
  ⟨(-457363880633286357831001059771430870840029 : ℚ), (-58908042449790408201719929994079371205758 : ℚ), (561341831203694702800000000000000000000000 : ℚ), (-58908042449790408201719929994079371205758 : ℚ), (1018705711836981060631001059771430870840029 : ℚ)⟩

theorem sign_064_00 :
    polynomial_064.BernsteinNonnegCheck (1433/2048 : ℚ) (1697/2048 : ℚ) := by
  norm_num [polynomial_064, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_064_00

def entry_064_00 : CachedQuarticSign :=
  ⟨polynomial_064, (1433/2048 : ℚ), (1697/2048 : ℚ),
    false, .leaf⟩

theorem entry_064_00_checked : entry_064_00.Check := by
  change polynomial_064.BernsteinNonnegCheck (1433/2048 : ℚ) (1697/2048 : ℚ)
  exact sign_064_00

def polynomial_065 : Quartic :=
  ⟨(-460136119754489454897761894258530987913047 : ℚ), (-132864954793510332821413543563234866693894 : ℚ), (1082478975658466580400000000000000000000000 : ℚ), (-132864954793510332821413543563234866693894 : ℚ), (1542615095412956035297761894258530987913047 : ℚ)⟩

theorem sign_065_00 :
    polynomial_065.BernsteinNonnegCheck (633/1024 : ℚ) (2895/4096 : ℚ) := by
  norm_num [polynomial_065, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_065_00

def entry_065_00 : CachedQuarticSign :=
  ⟨polynomial_065, (633/1024 : ℚ), (2895/4096 : ℚ),
    false, .leaf⟩

theorem entry_065_00_checked : entry_065_00.Check := by
  change polynomial_065.BernsteinNonnegCheck (633/1024 : ℚ) (2895/4096 : ℚ)
  exact sign_065_00

def polynomial_066 : Quartic :=
  ⟨(-471806604312643676569772115558465737091 : ℚ), (1656201663620838231293629760259108045562 : ℚ), (-699073692924346443200000000000000000000 : ℚ), (-1299998217082244104706370239740891954438 : ℚ), (-278757808035597589030227884441534262909 : ℚ)⟩

theorem sign_066_00 :
    polynomial_066.BernsteinNonnegCheck (1795/4096 : ℚ) (1001/2048 : ℚ) := by
  norm_num [polynomial_066, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_066_00

def entry_066_00 : CachedQuarticSign :=
  ⟨polynomial_066, (1795/4096 : ℚ), (1001/2048 : ℚ),
    false, .leaf⟩

theorem entry_066_00_checked : entry_066_00.Check := by
  change polynomial_066.BernsteinNonnegCheck (1795/4096 : ℚ) (1001/2048 : ℚ)
  exact sign_066_00

def polynomial_067 : Quartic :=
  ⟨(-472440062981729734413346383927807741539422923 : ℚ), (2421400521884473008331859121491486794772845846 : ℚ), (878661113774749810064400000000000000000000000 : ℚ), (-3014855808232937740485740878508513205227154154 : ℚ), (-324076241228161993810253616072192258460577077 : ℚ)⟩

theorem sign_067_00 :
    polynomial_067.BernsteinNonnegCheck (647/2048 : ℚ) (1119/2048 : ℚ) := by
  norm_num [polynomial_067, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_067_00

def entry_067_00 : CachedQuarticSign :=
  ⟨polynomial_067, (647/2048 : ℚ), (1119/2048 : ℚ),
    false, .leaf⟩

theorem entry_067_00_checked : entry_067_00.Check := by
  change polynomial_067.BernsteinNonnegCheck (647/2048 : ℚ) (1119/2048 : ℚ)
  exact sign_067_00

def polynomial_068 : Quartic :=
  ⟨(-496817 : ℚ), (62696 : ℚ), (496817 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_068_00 :
    polynomial_068.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_068, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_068_00

def entry_068_00 : CachedQuarticSign :=
  ⟨polynomial_068, (1923/2048 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_068_00_checked : entry_068_00.Check := by
  change polynomial_068.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_068_00

def polynomial_069 : Quartic :=
  ⟨(-50530083183256161829380423888227761880596241 : ℚ), (3969762973125203197209514750000000000000000000 : ℚ), (-9147905213605974575035376423888227761880596241 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_069_00 :
    polynomial_069.BernsteinNonnegCheck (161/4096 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_069, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_069_00

def entry_069_00 : CachedQuarticSign :=
  ⟨polynomial_069, (161/4096 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_069_00_checked : entry_069_00.Check := by
  change polynomial_069.BernsteinNonnegCheck (161/4096 : ℚ) (1293/4096 : ℚ)
  exact sign_069_00

def polynomial_070 : Quartic :=
  ⟨(-51801572107092506942814216568780039565075776563 : ℚ), (81799838468774307389409002750000000000000000000 : ℚ), (53055932110531279267538284681219960434924223437 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_070_00 :
    polynomial_070.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_070, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_070_00

def entry_070_00 : CachedQuarticSign :=
  ⟨polynomial_070, (247/512 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_070_00_checked : entry_070_00.Check := by
  change polynomial_070.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ)
  exact sign_070_00

def polynomial_071 : Quartic :=
  ⟨(-521761519082888026474657188740769567 : ℚ), (5249586921796186142180070715702648214 : ℚ), (-11263870658378688489349714591855169426 : ℚ), (1496787788011013857819929284297351786 : ℚ), (-1877418025410488026474657188740769567 : ℚ)⟩

theorem sign_071_00 :
    polynomial_071.BernsteinNonnegCheck (619/4096 : ℚ) (837/4096 : ℚ) := by
  norm_num [polynomial_071, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_071_00

def entry_071_00 : CachedQuarticSign :=
  ⟨polynomial_071, (619/4096 : ℚ), (837/4096 : ℚ),
    false, .leaf⟩

theorem entry_071_00_checked : entry_071_00.Check := by
  change polynomial_071.BernsteinNonnegCheck (619/4096 : ℚ) (837/4096 : ℚ)
  exact sign_071_00

def polynomial_072 : Quartic :=
  ⟨(-524067 : ℚ), (1406164 : ℚ), (524067 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_072_00 :
    polynomial_072.BernsteinNonnegCheck (1387/4096 : ℚ) (1423/2048 : ℚ) := by
  norm_num [polynomial_072, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_072_00

def entry_072_00 : CachedQuarticSign :=
  ⟨polynomial_072, (1387/4096 : ℚ), (1423/2048 : ℚ),
    false, .leaf⟩

theorem entry_072_00_checked : entry_072_00.Check := by
  change polynomial_072.BernsteinNonnegCheck (1387/4096 : ℚ) (1423/2048 : ℚ)
  exact sign_072_00

def polynomial_073 : Quartic :=
  ⟨(-532931298702208403874432931911833971443 : ℚ), (4534358567657691809577697213260586057114 : ℚ), (-7946389703878202982000000000000000000000 : ℚ), (476466466399806271577697213260586057114 : ℚ), (4477893729733571243874432931911833971443 : ℚ)⟩

theorem sign_073_00 :
    polynomial_073.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_073, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_073_00

def entry_073_00 : CachedQuarticSign :=
  ⟨polynomial_073, (65/128 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_073_00_checked : entry_073_00.Check := by
  change polynomial_073.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ)
  exact sign_073_00

def polynomial_074 : Quartic :=
  ⟨(-538092784506937993380638472577 : ℚ), (7152296588781420436149865054846 : ℚ), (1076185569013875986761276945154 : ℚ), (-7152296588781420436149865054846 : ℚ), (-538092784506937993380638472577 : ℚ)⟩

theorem sign_074_00 :
    polynomial_074.BernsteinNonnegCheck (633/1024 : ℚ) (3355/4096 : ℚ) := by
  norm_num [polynomial_074, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_074_00

def entry_074_00 : CachedQuarticSign :=
  ⟨polynomial_074, (633/1024 : ℚ), (3355/4096 : ℚ),
    false, .leaf⟩

theorem entry_074_00_checked : entry_074_00.Check := by
  change polynomial_074.BernsteinNonnegCheck (633/1024 : ℚ) (3355/4096 : ℚ)
  exact sign_074_00

def polynomial_075 : Quartic :=
  ⟨(-540223 : ℚ), (1419504 : ℚ), (540223 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_075_00 :
    polynomial_075.BernsteinNonnegCheck (1433/2048 : ℚ) (743/1024 : ℚ) := by
  norm_num [polynomial_075, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_075_00

def entry_075_00 : CachedQuarticSign :=
  ⟨polynomial_075, (1433/2048 : ℚ), (743/1024 : ℚ),
    false, .leaf⟩

theorem entry_075_00_checked : entry_075_00.Check := by
  change polynomial_075.BernsteinNonnegCheck (1433/2048 : ℚ) (743/1024 : ℚ)
  exact sign_075_00

def polynomial_076 : Quartic :=
  ⟨(-54199827241560779748448796168837731669651751 : ℚ), (-54458597794399988353602575796843873730619698 : ℚ), (216367148350284104006000000000000000000000000 : ℚ), (-45233105466449538099202575796843873730619698 : ℚ), (-13376733506449555122351203831162268330348249 : ℚ)⟩

theorem sign_076_00 :
    polynomial_076.BernsteinNonnegCheck (3005/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_076, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_076_00

def entry_076_00 : CachedQuarticSign :=
  ⟨polynomial_076, (3005/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_076_00_checked : entry_076_00.Check := by
  change polynomial_076.BernsteinNonnegCheck (3005/4096 : ℚ) (127/128 : ℚ)
  exact sign_076_00

def polynomial_077 : Quartic :=
  ⟨(-5427867026031939848234 : ℚ), (19813871168888210531181 : ℚ), (-6229288667936120303532 : ℚ), (185928831111789468819 : ℚ), (-5427967026031939848234 : ℚ)⟩

theorem sign_077_00 :
    polynomial_077.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_077, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_077_00

def entry_077_00 : CachedQuarticSign :=
  ⟨polynomial_077, (247/512 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_077_00_checked : entry_077_00.Check := by
  change polynomial_077.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ)
  exact sign_077_00

def polynomial_078 : Quartic :=
  ⟨(-5427867026031939848234 : ℚ), (20052627648888210531181 : ℚ), (-6019293127936120303532 : ℚ), (-52827648888210531181 : ℚ), (-5427967026031939848234 : ℚ)⟩

theorem sign_078_00 :
    polynomial_078.BernsteinNonnegCheck (1795/4096 : ℚ) (1001/2048 : ℚ) := by
  norm_num [polynomial_078, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_078_00

def entry_078_00 : CachedQuarticSign :=
  ⟨polynomial_078, (1795/4096 : ℚ), (1001/2048 : ℚ),
    false, .leaf⟩

theorem entry_078_00_checked : entry_078_00.Check := by
  change polynomial_078.BernsteinNonnegCheck (1795/4096 : ℚ) (1001/2048 : ℚ)
  exact sign_078_00

def polynomial_079 : Quartic :=
  ⟨(-5640072335450098181994573020786412100409 : ℚ), (63232429651749589599471459379867531816818 : ℚ), (54343684662635318670400000000000000000000 : ℚ), (-50615870455421316134928540620132468183182 : ℚ), (24901507406784023380394573020786412100409 : ℚ)⟩

theorem sign_079_00 :
    polynomial_079.BernsteinNonnegCheck (343/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_079, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_079_00

def entry_079_00 : CachedQuarticSign :=
  ⟨polynomial_079, (343/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_079_00_checked : entry_079_00.Check := by
  change polynomial_079.BernsteinNonnegCheck (343/4096 : ℚ) (679/2048 : ℚ)
  exact sign_079_00

def cache : List CachedQuarticSign :=
  [entry_064_00, entry_065_00, entry_066_00, entry_067_00, entry_068_00, entry_069_00, entry_070_00, entry_071_00, entry_072_00, entry_073_00, entry_074_00, entry_075_00, entry_076_00, entry_077_00, entry_078_00, entry_079_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_064_00.Check ∧ entry_065_00.Check ∧ entry_066_00.Check ∧ entry_067_00.Check ∧ entry_068_00.Check ∧ entry_069_00.Check ∧ entry_070_00.Check ∧ entry_071_00.Check ∧ entry_072_00.Check ∧ entry_073_00.Check ∧ entry_074_00.Check ∧ entry_075_00.Check ∧ entry_076_00.Check ∧ entry_077_00.Check ∧ entry_078_00.Check ∧ entry_079_00.Check ∧ True
  exact ⟨entry_064_00_checked, entry_065_00_checked, entry_066_00_checked, entry_067_00_checked, entry_068_00_checked, entry_069_00_checked, entry_070_00_checked, entry_071_00_checked, entry_072_00_checked, entry_073_00_checked, entry_074_00_checked, entry_075_00_checked, entry_076_00_checked, entry_077_00_checked, entry_078_00_checked, entry_079_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk04
