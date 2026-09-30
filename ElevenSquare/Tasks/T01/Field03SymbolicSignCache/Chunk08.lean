import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk08
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_128 : Quartic :=
  ⟨(163000353 : ℚ), (-1054067518 : ℚ), (0 : ℚ), (-1054067518 : ℚ), (-163000353 : ℚ)⟩

theorem sign_128_00 :
    polynomial_128.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_128, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_128_00

def entry_128_00 : CachedQuarticSign :=
  ⟨polynomial_128, (161/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_128_00_checked : entry_128_00.Check := by
  change polynomial_128.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ)
  exact sign_128_00

def polynomial_129 : Quartic :=
  ⟨(1660913740298208513709983415000 : ℚ), (-4514624475896221133339455693187 : ℚ), (7420819400250000000000000000000 : ℚ), (-5815524475896221133339455693187 : ℚ), (-1660944340048208513709983415000 : ℚ)⟩

theorem sign_129_00 :
    polynomial_129.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_129, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_129_00

def entry_129_00 : CachedQuarticSign :=
  ⟨polynomial_129, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_129_00_checked : entry_129_00.Check := by
  change polynomial_129.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_129_00

def polynomial_130 : Quartic :=
  ⟨(16770697 : ℚ), (36356334 : ℚ), (-16770697 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_130_00 :
    polynomial_130.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_130, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_130_00

def entry_130_00 : CachedQuarticSign :=
  ⟨polynomial_130, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_130_00_checked : entry_130_00.Check := by
  change polynomial_130.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_130_00

def polynomial_131 : Quartic :=
  ⟨(1697956133681500034685617210405362490859 : ℚ), (3604284344988466887623996183367184000000 : ℚ), (-12741247743515865441026780234482950945154 : ℚ), (10015016591784968312376003816632816000000 : ℚ), (-1706869104331782365314382789594637509141 : ℚ)⟩

theorem sign_131_00 :
    polynomial_131.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_131, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_131_00

def entry_131_00 : CachedQuarticSign :=
  ⟨polynomial_131, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_131_00_checked : entry_131_00.Check := by
  change polynomial_131.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_131_00

def polynomial_132 : Quartic :=
  ⟨(17203962651399772535055377921423013 : ℚ), (-22989573885099226136373434516151066 : ℚ), (23618117911600000000000000000000000 : ℚ), (-10990189885099226136373434516151066 : ℚ), (-17204140739799772535055377921423013 : ℚ)⟩

theorem sign_132_00 :
    polynomial_132.BernsteinNonnegCheck (2973/4096 : ℚ) (1697/2048 : ℚ) := by
  norm_num [polynomial_132, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_132_00

def entry_132_00 : CachedQuarticSign :=
  ⟨polynomial_132, (2973/4096 : ℚ), (1697/2048 : ℚ),
    false, .leaf⟩

theorem entry_132_00_checked : entry_132_00.Check := by
  change polynomial_132.BernsteinNonnegCheck (2973/4096 : ℚ) (1697/2048 : ℚ)
  exact sign_132_00

def polynomial_133 : Quartic :=
  ⟨(174435 : ℚ), (244798 : ℚ), (-174435 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_133_00 :
    polynomial_133.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_133, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_133_00

def entry_133_00 : CachedQuarticSign :=
  ⟨polynomial_133, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_133_00_checked : entry_133_00.Check := by
  change polynomial_133.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_133_00

def polynomial_134 : Quartic :=
  ⟨(178307 : ℚ), (2534 : ℚ), (-178307 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_134_00 :
    polynomial_134.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_134, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_134_00

def entry_134_00 : CachedQuarticSign :=
  ⟨polynomial_134, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_134_00_checked : entry_134_00.Check := by
  change polynomial_134.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_134_00

def polynomial_135 : Quartic :=
  ⟨(18178167 : ℚ), (-33541394 : ℚ), (-18178167 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_135_00 :
    polynomial_135.BernsteinPosCheck (1/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_135, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_135_00

def entry_135_00 : CachedQuarticSign :=
  ⟨polynomial_135, (1/4096 : ℚ), (897/2048 : ℚ),
    true, .leaf⟩

theorem entry_135_00_checked : entry_135_00.Check := by
  change polynomial_135.BernsteinPosCheck (1/4096 : ℚ) (897/2048 : ℚ)
  exact sign_135_00

def polynomial_136 : Quartic :=
  ⟨(18178167 : ℚ), (-33541394 : ℚ), (0 : ℚ), (-33541394 : ℚ), (-18178167 : ℚ)⟩

theorem sign_136_00 :
    polynomial_136.BernsteinNonnegCheck (1387/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_136, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_136_00

def entry_136_00 : CachedQuarticSign :=
  ⟨polynomial_136, (1387/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_136_00_checked : entry_136_00.Check := by
  change polynomial_136.BernsteinNonnegCheck (1387/4096 : ℚ) (897/2048 : ℚ)
  exact sign_136_00

def polynomial_137 : Quartic :=
  ⟨(183822941351973937117809762962461507729 : ℚ), (3886965970909274133000000000000000000000 : ℚ), (-6430546199109576062882190237037538492271 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_137_00 :
    polynomial_137.BernsteinNonnegCheck (1/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_137, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_137_00

def entry_137_00 : CachedQuarticSign :=
  ⟨polynomial_137, (1/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_137_00_checked : entry_137_00.Check := by
  change polynomial_137.BernsteinNonnegCheck (1/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_137_00

def polynomial_138 : Quartic :=
  ⟨(18610575973062006619361527423 : ℚ), (402129505061420436149865054846 : ℚ), (-4198632001706124013238723054846 : ℚ), (14877717694938579563850134945154 : ℚ), (-7621313024026937993380638472577 : ℚ)⟩

theorem sign_138_00 :
    polynomial_138.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_138, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_138_00

def entry_138_00 : CachedQuarticSign :=
  ⟨polynomial_138, (161/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_138_00_checked : entry_138_00.Check := by
  change polynomial_138.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ)
  exact sign_138_00

theorem sign_138_01 :
    polynomial_138.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_138, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_138_01

def entry_138_01 : CachedQuarticSign :=
  ⟨polynomial_138, (633/1024 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_138_01_checked : entry_138_01.Check := by
  change polynomial_138.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ)
  exact sign_138_01

def polynomial_139 : Quartic :=
  ⟨(18610575973062006619361527423 : ℚ), (402129505061420436149865054846 : ℚ), (-7616809502186124013238723054846 : ℚ), (14877717694938579563850134945154 : ℚ), (-7621313024026937993380638472577 : ℚ)⟩

theorem sign_139_00 :
    polynomial_139.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_139, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_139_00

def entry_139_00 : CachedQuarticSign :=
  ⟨polynomial_139, (1923/2048 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_139_00_checked : entry_139_00.Check := by
  change polynomial_139.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_139_00

def polynomial_140 : Quartic :=
  ⟨(1873363703764257697242572506767 : ℚ), (-3371812900550016352912314346594 : ℚ), (73196192471484605514854986466 : ℚ), (3371812900550016352912314346594 : ℚ), (-1946559896235742302757427493233 : ℚ)⟩

theorem sign_140_00 :
    polynomial_140.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_140, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_140_00

def entry_140_00 : CachedQuarticSign :=
  ⟨polynomial_140, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_140_00_checked : entry_140_00.Check := by
  change polynomial_140.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_140_00

def polynomial_141 : Quartic :=
  ⟨(188537562480438785281597537909179651817 : ℚ), (1095725220334069520000000000000000000000 : ℚ), (-2944759757981383038718402462090820348183 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_141_00 :
    polynomial_141.BernsteinNonnegCheck (1/4096 : ℚ) (837/4096 : ℚ) := by
  norm_num [polynomial_141, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_141_00

def entry_141_00 : CachedQuarticSign :=
  ⟨polynomial_141, (1/4096 : ℚ), (837/4096 : ℚ),
    false, .leaf⟩

theorem entry_141_00_checked : entry_141_00.Check := by
  change polynomial_141.BernsteinNonnegCheck (1/4096 : ℚ) (837/4096 : ℚ)
  exact sign_141_00

def polynomial_142 : Quartic :=
  ⟨(1886834102720445492268678268165919336959 : ℚ), (3678341506014479969481272228854241679000 : ℚ), (-15844822535664215391843733893425607379754 : ℚ), (9940959430758955230518727771145758321000 : ℚ), (-1517991135292836907731321731834080663041 : ℚ)⟩

theorem sign_142_00 :
    polynomial_142.BernsteinNonnegCheck (717/2048 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_142, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_142_00

def entry_142_00 : CachedQuarticSign :=
  ⟨polynomial_142, (717/2048 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_142_00_checked : entry_142_00.Check := by
  change polynomial_142.BernsteinNonnegCheck (717/2048 : ℚ) (2531/4096 : ℚ)
  exact sign_142_00

def cache : List CachedQuarticSign :=
  [entry_128_00, entry_129_00, entry_130_00, entry_131_00, entry_132_00, entry_133_00, entry_134_00, entry_135_00, entry_136_00, entry_137_00, entry_138_00, entry_138_01, entry_139_00, entry_140_00, entry_141_00, entry_142_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_128_00.Check ∧ entry_129_00.Check ∧ entry_130_00.Check ∧ entry_131_00.Check ∧ entry_132_00.Check ∧ entry_133_00.Check ∧ entry_134_00.Check ∧ entry_135_00.Check ∧ entry_136_00.Check ∧ entry_137_00.Check ∧ entry_138_00.Check ∧ entry_138_01.Check ∧ entry_139_00.Check ∧ entry_140_00.Check ∧ entry_141_00.Check ∧ entry_142_00.Check ∧ True
  exact ⟨entry_128_00_checked, entry_129_00_checked, entry_130_00_checked, entry_131_00_checked, entry_132_00_checked, entry_133_00_checked, entry_134_00_checked, entry_135_00_checked, entry_136_00_checked, entry_137_00_checked, entry_138_00_checked, entry_138_01_checked, entry_139_00_checked, entry_140_00_checked, entry_141_00_checked, entry_142_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk08
