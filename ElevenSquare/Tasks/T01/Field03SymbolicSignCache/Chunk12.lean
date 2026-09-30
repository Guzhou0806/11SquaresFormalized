import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk12
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_188 : Quartic :=
  ⟨(40903587675742302757427493233 : ℚ), (-3270641309983647087685653406 : ℚ), (-2162512600231484605514854986466 : ℚ), (7643194241309983647087685653406 : ℚ), (-3779058212324257697242572506767 : ℚ)⟩

theorem sign_188_00 :
    polynomial_188.BernsteinNonnegCheck (619/4096 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_188, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_188_00

def entry_188_00 : CachedQuarticSign :=
  ⟨polynomial_188, (619/4096 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_188_00_checked : entry_188_00.Check := by
  change polynomial_188.BernsteinNonnegCheck (619/4096 : ℚ) (1293/4096 : ℚ)
  exact sign_188_00

theorem sign_188_01 :
    polynomial_188.BernsteinNonnegCheck (647/2048 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_188, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_188_01

def entry_188_01 : CachedQuarticSign :=
  ⟨polynomial_188, (647/2048 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_188_01_checked : entry_188_01.Check := by
  change polynomial_188.BernsteinNonnegCheck (647/2048 : ℚ) (897/2048 : ℚ)
  exact sign_188_01

def polynomial_189 : Quartic :=
  ⟨(40903587675742302757427493233 : ℚ), (3819961800000000000000000000000 : ℚ), (-3779058212324257697242572506767 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_189_00 :
    polynomial_189.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_189, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_189_00

def entry_189_00 : CachedQuarticSign :=
  ⟨polynomial_189, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_189_00_checked : entry_189_00.Check := by
  change polynomial_189.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_189_00

def polynomial_190 : Quartic :=
  ⟨(40903587675742302757427493233 : ℚ), (38200000000000000000000000 : ℚ), (-3779058212324257697242572506767 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_190_00 :
    polynomial_190.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ) := by
  norm_num [polynomial_190, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_190_00

def entry_190_00 : CachedQuarticSign :=
  ⟨polynomial_190, (1/4096 : ℚ), (315/4096 : ℚ),
    false, .leaf⟩

theorem entry_190_00_checked : entry_190_00.Check := by
  change polynomial_190.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ)
  exact sign_190_00

def polynomial_191 : Quartic :=
  ⟨(409284477902837879794082390969147761 : ℚ), (-1062777506305188742415154027016581943 : ℚ), (50166606359111768489604050995305960 : ℚ), (-1000947678365611257584845972983418057 : ℚ), (-576498376045762120205917609030852239 : ℚ)⟩

theorem sign_191_00 :
    polynomial_191.BernsteinNonnegCheck (677/4096 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_191, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_191_00

def entry_191_00 : CachedQuarticSign :=
  ⟨polynomial_191, (677/4096 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_191_00_checked : entry_191_00.Check := by
  change polynomial_191.BernsteinNonnegCheck (677/4096 : ℚ) (1293/4096 : ℚ)
  exact sign_191_00

def polynomial_192 : Quartic :=
  ⟨(40977789788097035919224523882001744 : ℚ), (-97595247301878837872371943483044563 : ℚ), (300346819314200000000000000000000000 : ℚ), (-303971893301878837872371943483044563 : ℚ), (62208515526102964080775476117998256 : ℚ)⟩

theorem sign_192_00 :
    polynomial_192.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_192, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_192_00

def entry_192_00 : CachedQuarticSign :=
  ⟨polynomial_192, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_192_00_checked : entry_192_00.Check := by
  change polynomial_192.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_192_00

def polynomial_193 : Quartic :=
  ⟨(4131 : ℚ), (1063111 : ℚ), (-4131 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_193_00 :
    polynomial_193.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_193, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_193_00

def entry_193_00 : CachedQuarticSign :=
  ⟨polynomial_193, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_193_00_checked : entry_193_00.Check := by
  change polynomial_193.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_193_00

def polynomial_194 : Quartic :=
  ⟨(4305491440000000000000000000 : ℚ), (243813505609289781925067472577 : ℚ), (-3791351630933875986761276945154 : ℚ), (7396110094390710218074932527423 : ℚ), (-3815656308560000000000000000000 : ℚ)⟩

theorem sign_194_00 :
    polynomial_194.BernsteinNonnegCheck (1/4096 : ℚ) (189/2048 : ℚ) := by
  norm_num [polynomial_194, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_194_00

def entry_194_00 : CachedQuarticSign :=
  ⟨polynomial_194, (1/4096 : ℚ), (189/2048 : ℚ),
    false, .leaf⟩

theorem entry_194_00_checked : entry_194_00.Check := by
  change polynomial_194.BernsteinNonnegCheck (1/4096 : ℚ) (189/2048 : ℚ)
  exact sign_194_00

theorem sign_194_01 :
    polynomial_194.BernsteinNonnegCheck (3301/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_194, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_194_01

def entry_194_01 : CachedQuarticSign :=
  ⟨polynomial_194, (3301/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_194_01_checked : entry_194_01.Check := by
  change polynomial_194.BernsteinNonnegCheck (3301/4096 : ℚ) (127/128 : ℚ)
  exact sign_194_01

def polynomial_195 : Quartic :=
  ⟨(43485053997546075226751499758427863 : ℚ), (613149001943349445911718382592718284 : ℚ), (-31601450840200000000000000000000000 : ℚ), (-3416374178056650554088281617407281716 : ℚ), (4017558355162253924773248500241572137 : ℚ)⟩

theorem sign_195_00 :
    polynomial_195.BernsteinNonnegCheck (619/4096 : ℚ) (1605/4096 : ℚ) := by
  norm_num [polynomial_195, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_195_00

def entry_195_00 : CachedQuarticSign :=
  ⟨polynomial_195, (619/4096 : ℚ), (1605/4096 : ℚ),
    false, .leaf⟩

theorem entry_195_00_checked : entry_195_00.Check := by
  change polynomial_195.BernsteinNonnegCheck (619/4096 : ℚ) (1605/4096 : ℚ)
  exact sign_195_00

def polynomial_196 : Quartic :=
  ⟨(445666667 : ℚ), (1782666666 : ℚ), (-445666667 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_196_00 :
    polynomial_196.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_196, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_196_00

def entry_196_00 : CachedQuarticSign :=
  ⟨polynomial_196, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_196_00_checked : entry_196_00.Check := by
  change polynomial_196.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_196_00

def polynomial_197 : Quartic :=
  ⟨(445666667 : ℚ), (1782666666 : ℚ), (0 : ℚ), (1782666666 : ℚ), (-445666667 : ℚ)⟩

theorem sign_197_00 :
    polynomial_197.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_197, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_197_00

def entry_197_00 : CachedQuarticSign :=
  ⟨polynomial_197, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_197_00_checked : entry_197_00.Check := by
  change polynomial_197.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_197_00

def polynomial_198 : Quartic :=
  ⟨(4472545770000000000000000000 : ℚ), (2968944188413062006619361527423 : ℚ), (-11048810803398579563850134945154 : ℚ), (4670979411586937993380638472577 : ℚ), (-3815489254230000000000000000000 : ℚ)⟩

theorem sign_198_00 :
    polynomial_198.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_198, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_198_00

def entry_198_00 : CachedQuarticSign :=
  ⟨polynomial_198, (161/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_198_00_checked : entry_198_00.Check := by
  change polynomial_198.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ)
  exact sign_198_00

def polynomial_199 : Quartic :=
  ⟨(447710236031939848234 : ℚ), (9021226061111789468819 : ℚ), (-895420472063879696468 : ℚ), (-9021226061111789468819 : ℚ), (447710236031939848234 : ℚ)⟩

theorem sign_199_00 :
    polynomial_199.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_199, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_199_00

def entry_199_00 : CachedQuarticSign :=
  ⟨polynomial_199, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_199_00_checked : entry_199_00.Check := by
  change polynomial_199.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_199_00

def polynomial_200 : Quartic :=
  ⟨(49040606827028991264473849991790919759 : ℚ), (-24079777243190308242712784273681236456 : ℚ), (-275720438041274076388461979444584031242 : ℚ), (301836613755355108242712784273681236456 : ℚ), (-79084955690469408735526150008209080241 : ℚ)⟩

theorem sign_200_00 :
    polynomial_200.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_200, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_200_00

def entry_200_00 : CachedQuarticSign :=
  ⟨polynomial_200, (677/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_200_00_checked : entry_200_00.Check := by
  change polynomial_200.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ)
  exact sign_200_00

def polynomial_201 : Quartic :=
  ⟨(50633 : ℚ), (930888 : ℚ), (-50633 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_201_00 :
    polynomial_201.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_201, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_201_00

def entry_201_00 : CachedQuarticSign :=
  ⟨polynomial_201, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_201_00_checked : entry_201_00.Check := by
  change polynomial_201.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_201_00

def cache : List CachedQuarticSign :=
  [entry_188_00, entry_188_01, entry_189_00, entry_190_00, entry_191_00, entry_192_00, entry_193_00, entry_194_00, entry_194_01, entry_195_00, entry_196_00, entry_197_00, entry_198_00, entry_199_00, entry_200_00, entry_201_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_188_00.Check ∧ entry_188_01.Check ∧ entry_189_00.Check ∧ entry_190_00.Check ∧ entry_191_00.Check ∧ entry_192_00.Check ∧ entry_193_00.Check ∧ entry_194_00.Check ∧ entry_194_01.Check ∧ entry_195_00.Check ∧ entry_196_00.Check ∧ entry_197_00.Check ∧ entry_198_00.Check ∧ entry_199_00.Check ∧ entry_200_00.Check ∧ entry_201_00.Check ∧ True
  exact ⟨entry_188_00_checked, entry_188_01_checked, entry_189_00_checked, entry_190_00_checked, entry_191_00_checked, entry_192_00_checked, entry_193_00_checked, entry_194_00_checked, entry_194_01_checked, entry_195_00_checked, entry_196_00_checked, entry_197_00_checked, entry_198_00_checked, entry_199_00_checked, entry_200_00_checked, entry_201_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk12
