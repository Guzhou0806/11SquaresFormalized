import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk14
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_218 : Quartic :=
  ⟨(71815146893895939672751270900336183 : ℚ), (2250079820184977658757015081547082985 : ℚ), (-2695768039610820686097225020721921028 : ℚ), (137324680770022341242984918452917015 : ℚ), (-90081810102204060327248729099663817 : ℚ)⟩

theorem sign_218_00 :
    polynomial_218.BernsteinNonnegCheck (619/4096 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_218, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_218_00

def entry_218_00 : CachedQuarticSign :=
  ⟨polynomial_218, (619/4096 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_218_00_checked : entry_218_00.Check := by
  change polynomial_218.BernsteinNonnegCheck (619/4096 : ℚ) (1293/4096 : ℚ)
  exact sign_218_00

def polynomial_219 : Quartic :=
  ⟨(72886533557182394350133871876172896328004143 : ℚ), (328421634083319797721200000000000000000000000 : ℚ), (-2395820670634035074747466128123827103671995857 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_219_00 :
    polynomial_219.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_219, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_219_00

def entry_219_00 : CachedQuarticSign :=
  ⟨polynomial_219, (1/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_219_00_checked : entry_219_00.Check := by
  change polynomial_219.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ)
  exact sign_219_00

def polynomial_220 : Quartic :=
  ⟨(739536421133187706998802019032017303 : ℚ), (-19315162961038760027644407277960385906 : ℚ), (12151609998319600000000000000000000000 : ℚ), (-27500452681038760027644407277960385906 : ℚ), (3353027217186412293001197980967982697 : ℚ)⟩

theorem sign_220_00 :
    polynomial_220.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ) := by
  norm_num [polynomial_220, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_220_00

def entry_220_00 : CachedQuarticSign :=
  ⟨polynomial_220, (1/4096 : ℚ), (5/128 : ℚ),
    false, .leaf⟩

theorem entry_220_00_checked : entry_220_00.Check := by
  change polynomial_220.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ)
  exact sign_220_00

def polynomial_221 : Quartic :=
  ⟨(7541906220000000000000000000 : ℚ), (3618935247469289781925067472577 : ℚ), (-3797824460493875986761276945154 : ℚ), (-3618858847469289781925067472577 : ℚ), (-3812419893780000000000000000000 : ℚ)⟩

theorem sign_221_00 :
    polynomial_221.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ) := by
  norm_num [polynomial_221, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_221_00

def entry_221_00 : CachedQuarticSign :=
  ⟨polynomial_221, (1/4096 : ℚ), (315/4096 : ℚ),
    false, .leaf⟩

theorem entry_221_00_checked : entry_221_00.Check := by
  change polynomial_221.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ)
  exact sign_221_00

def polynomial_222 : Quartic :=
  ⟨(7574756735092778746741287090499823 : ℚ), (-27192723827807274157503473920147181 : ℚ), (13063118218586361620943470038245024 : ℚ), (57190583858607274157503473920147181 : ℚ), (-21947522807507221253258712909500177 : ℚ)⟩

theorem sign_222_00 :
    polynomial_222.BernsteinNonnegCheck (1/4096 : ℚ) (1119/2048 : ℚ) := by
  norm_num [polynomial_222, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_222_00

def entry_222_00 : CachedQuarticSign :=
  ⟨polynomial_222, (1/4096 : ℚ), (1119/2048 : ℚ),
    false, .leaf⟩

theorem entry_222_00_checked : entry_222_00.Check := by
  change polynomial_222.BernsteinNonnegCheck (1/4096 : ℚ) (1119/2048 : ℚ)
  exact sign_222_00

def polynomial_223 : Quartic :=
  ⟨(77107540380056756273928152220889 : ℚ), (-272602619401262936988440762080000 : ℚ), (66265160781281143630213020761778 : ℚ), (552796215417262936988440762080000 : ℚ), (-191781081739943243726071847779111 : ℚ)⟩

theorem sign_223_00 :
    polynomial_223.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_223, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_223_00

def entry_223_00 : CachedQuarticSign :=
  ⟨polynomial_223, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_223_00_checked : entry_223_00.Check := by
  change polynomial_223.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_223_00

def polynomial_224 : Quartic :=
  ⟨(78001100643655707404720203693153010112781 : ℚ), (647891957877946096527261372357754990945562 : ℚ), (-758053855824765897800000000000000000000000 : ℚ), (277701889061060623343261372357754990945562 : ℚ), (303971446543092082923279796306846989887219 : ℚ)⟩

theorem sign_224_00 :
    polynomial_224.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_224, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_224_00

def entry_224_00 : CachedQuarticSign :=
  ⟨polynomial_224, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_224_00_checked : entry_224_00.Check := by
  change polynomial_224.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_224_00

def polynomial_225 : Quartic :=
  ⟨(78421667305151143121337803693153010112781 : ℚ), (376085039647607136592000000000000000000000 : ℚ), (-676690300469109256878662196306846989887219 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_225_00 :
    polynomial_225.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_225, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_225_00

def entry_225_00 : CachedQuarticSign :=
  ⟨polynomial_225, (1/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_225_00_checked : entry_225_00.Check := by
  change polynomial_225.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ)
  exact sign_225_00

def polynomial_226 : Quartic :=
  ⟨(78529003525728000000000000000000 : ℚ), (-190148501161481537387780940597643 : ℚ), (363219625840000000000000000000000 : ℚ), (-238537701161481537387780940597643 : ℚ), (-78530577685728000000000000000000 : ℚ)⟩

theorem sign_226_00 :
    polynomial_226.BernsteinNonnegCheck (1387/4096 : ℚ) (3355/4096 : ℚ) := by
  norm_num [polynomial_226, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_226_00

def entry_226_00 : CachedQuarticSign :=
  ⟨polynomial_226, (1387/4096 : ℚ), (3355/4096 : ℚ),
    false, .leaf⟩

theorem entry_226_00_checked : entry_226_00.Check := by
  change polynomial_226.BernsteinNonnegCheck (1387/4096 : ℚ) (3355/4096 : ℚ)
  exact sign_226_00

def polynomial_227 : Quartic :=
  ⟨(830410739925077901598614559432017303 : ℚ), (3949088960294371418518297709356476442 : ℚ), (-17638781418292114006199452598022461902 : ℚ), (4109796218778428581481702290643523558 : ℚ), (-3262152267177722098401385440567982697 : ℚ)⟩

theorem sign_227_00 :
    polynomial_227.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_227, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_227_00

def entry_227_00 : CachedQuarticSign :=
  ⟨polynomial_227, (75/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_227_00_checked : entry_227_00.Check := by
  change polynomial_227.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ)
  exact sign_227_00

def polynomial_228 : Quartic :=
  ⟨(846000543 : ℚ), (47751296 : ℚ), (307958914 : ℚ), (-47751296 : ℚ), (-1153959457 : ℚ)⟩

theorem sign_228_00 :
    polynomial_228.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_228, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_228_00

def entry_228_00 : CachedQuarticSign :=
  ⟨polynomial_228, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_228_00_checked : entry_228_00.Check := by
  change polynomial_228.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_228_00

def polynomial_229 : Quartic :=
  ⟨(891333333 : ℚ), (-891333334 : ℚ), (-891333333 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_229_00 :
    polynomial_229.BernsteinPosCheck (75/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_229, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_229_00

def entry_229_00 : CachedQuarticSign :=
  ⟨polynomial_229, (75/4096 : ℚ), (2531/4096 : ℚ),
    true, .leaf⟩

theorem entry_229_00_checked : entry_229_00.Check := by
  change polynomial_229.BernsteinPosCheck (75/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_229_00

def polynomial_230 : Quartic :=
  ⟨(899828834725558557791286101520523744663 : ℚ), (-883059191778689081936321887725396101649 : ℚ), (5922713210446658400000000000000000000000 : ℚ), (-883059191778689081936321887725396101649 : ℚ), (5022884375721099842208713898479476255337 : ℚ)⟩

theorem sign_230_00 :
    polynomial_230.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_230, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_230_00

def entry_230_00 : CachedQuarticSign :=
  ⟨polynomial_230, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_230_00_checked : entry_230_00.Check := by
  change polynomial_230.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_230_00

def polynomial_231 : Quartic :=
  ⟨(90530121814803930000000000000 : ℚ), (-360123816706087865666949872969 : ℚ), (698968472410500000000000000000 : ℚ), (-331974698200087865666949872969 : ℚ), (-90531939631503930000000000000 : ℚ)⟩

theorem sign_231_00 :
    polynomial_231.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_231, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_231_00

def entry_231_00 : CachedQuarticSign :=
  ⟨polynomial_231, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_231_00_checked : entry_231_00.Check := by
  change polynomial_231.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_231_00

def polynomial_232 : Quartic :=
  ⟨(92877098940460800000000000000000 : ℚ), (-75117906159387320220611558065243 : ℚ), (206428938224000000000000000000000 : ℚ), (90806493840612679779388441934757 : ℚ), (-92878960716460800000000000000000 : ℚ)⟩

theorem sign_232_00 :
    polynomial_232.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_232, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_232_00

def entry_232_00 : CachedQuarticSign :=
  ⟨polynomial_232, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_232_00_checked : entry_232_00.Check := by
  change polynomial_232.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_232_00

def polynomial_233 : Quartic :=
  ⟨(999702349696532239999842015973676169 : ℚ), (-6870930995841270879640951983451394944 : ℚ), (126497231112539902169810742082511153098 : ℚ), (-249380194039155529120359048016548605056 : ℚ), (-137878715906385867760000157984026323831 : ℚ)⟩

theorem sign_233_00 :
    polynomial_233.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_233, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_233_00

def entry_233_00 : CachedQuarticSign :=
  ⟨polynomial_233, (161/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_233_00_checked : entry_233_00.Check := by
  change polynomial_233.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ)
  exact sign_233_00

def cache : List CachedQuarticSign :=
  [entry_218_00, entry_219_00, entry_220_00, entry_221_00, entry_222_00, entry_223_00, entry_224_00, entry_225_00, entry_226_00, entry_227_00, entry_228_00, entry_229_00, entry_230_00, entry_231_00, entry_232_00, entry_233_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_218_00.Check ∧ entry_219_00.Check ∧ entry_220_00.Check ∧ entry_221_00.Check ∧ entry_222_00.Check ∧ entry_223_00.Check ∧ entry_224_00.Check ∧ entry_225_00.Check ∧ entry_226_00.Check ∧ entry_227_00.Check ∧ entry_228_00.Check ∧ entry_229_00.Check ∧ entry_230_00.Check ∧ entry_231_00.Check ∧ entry_232_00.Check ∧ entry_233_00.Check ∧ True
  exact ⟨entry_218_00_checked, entry_219_00_checked, entry_220_00_checked, entry_221_00_checked, entry_222_00_checked, entry_223_00_checked, entry_224_00_checked, entry_225_00_checked, entry_226_00_checked, entry_227_00_checked, entry_228_00_checked, entry_229_00_checked, entry_230_00_checked, entry_231_00_checked, entry_232_00_checked, entry_233_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk14
