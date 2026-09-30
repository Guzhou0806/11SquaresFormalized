import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk07
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_112 : Quartic :=
  ⟨(120501034738796889362741535225230965 : ℚ), (1612856218426291108517371294984037419 : ℚ), (1311080485369052752744405849016576772 : ℚ), (-2074963836089091108517371294984037419 : ℚ), (-1613845507636603110637258464774769035 : ℚ)⟩

theorem sign_112_00 :
    polynomial_112.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ) := by
  norm_num [polynomial_112, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_112_00

def entry_112_00 : CachedQuarticSign :=
  ⟨polynomial_112, (1/4096 : ℚ), (5/128 : ℚ),
    false, .leaf⟩

theorem entry_112_00_checked : entry_112_00.Check := by
  change polynomial_112.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ)
  exact sign_112_00

def polynomial_113 : Quartic :=
  ⟨(12063 : ℚ), (1056380 : ℚ), (-12063 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_113_00 :
    polynomial_113.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_113, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_113_00

def entry_113_00 : CachedQuarticSign :=
  ⟨polynomial_113, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_113_00_checked : entry_113_00.Check := by
  change polynomial_113.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_113_00

def polynomial_114 : Quartic :=
  ⟨(122399 : ℚ), (-348870 : ℚ), (-122399 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_114_00 :
    polynomial_114.BernsteinNonnegCheck (161/4096 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_114, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_114_00

def entry_114_00 : CachedQuarticSign :=
  ⟨polynomial_114, (161/4096 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_114_00_checked : entry_114_00.Check := by
  change polynomial_114.BernsteinNonnegCheck (161/4096 : ℚ) (1293/4096 : ℚ)
  exact sign_114_00

def polynomial_115 : Quartic :=
  ⟨(122724836731268864226672998896969164411 : ℚ), (-134465795672395064310327245798759546624 : ℚ), (2786200694796752073181790322767368106782 : ℚ), (-3270359442340887335689672754201240453376 : ℚ), (-3282100397462089935773327001103030835589 : ℚ)⟩

theorem sign_115_00 :
    polynomial_115.BernsteinNonnegCheck (1387/4096 : ℚ) (1605/4096 : ℚ) := by
  norm_num [polynomial_115, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_115_00

def entry_115_00 : CachedQuarticSign :=
  ⟨polynomial_115, (1387/4096 : ℚ), (1605/4096 : ℚ),
    false, .leaf⟩

theorem entry_115_00_checked : entry_115_00.Check := by
  change polynomial_115.BernsteinNonnegCheck (1387/4096 : ℚ) (1605/4096 : ℚ)
  exact sign_115_00

def polynomial_116 : Quartic :=
  ⟨(12935134076574315457401613507331621804142743 : ℚ), (-73826582788821256944202331505864605830061486 : ℚ), (28930558890820348587600000000000000000000000 : ℚ), (67331961514750924599797668494135394169938514 : ℚ), (18454106666737010899798386492668378195857257 : ℚ)⟩

theorem sign_116_00 :
    polynomial_116.BernsteinNonnegCheck (1/4096 : ℚ) (811/4096 : ℚ) := by
  norm_num [polynomial_116, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_116_00

def entry_116_00 : CachedQuarticSign :=
  ⟨polynomial_116, (1/4096 : ℚ), (811/4096 : ℚ),
    false, .leaf⟩

theorem entry_116_00_checked : entry_116_00.Check := by
  change polynomial_116.BernsteinNonnegCheck (1/4096 : ℚ) (811/4096 : ℚ)
  exact sign_116_00

def polynomial_117 : Quartic :=
  ⟨(1303822317916772639854382765364257562719 : ℚ), (17997984385687108304329712330696748750142 : ℚ), (-21942242439492937624000000000000000000000 : ℚ), (17031964246634705136329712330696748750142 : ℚ), (6486260802621121032145617234635742437281 : ℚ)⟩

theorem sign_117_00 :
    polynomial_117.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_117, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_117_00

def entry_117_00 : CachedQuarticSign :=
  ⟨polynomial_117, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_117_00_checked : entry_117_00.Check := by
  change polynomial_117.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_117_00

def polynomial_118 : Quartic :=
  ⟨(131644 : ℚ), (460865 : ℚ), (-131644 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_118_00 :
    polynomial_118.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_118, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_118_00

def entry_118_00 : CachedQuarticSign :=
  ⟨polynomial_118, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_118_00_checked : entry_118_00.Check := by
  change polynomial_118.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_118_00

def polynomial_119 : Quartic :=
  ⟨(132040 : ℚ), (-618971 : ℚ), (-132040 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_119_00 :
    polynomial_119.BernsteinNonnegCheck (619/4096 : ℚ) (837/4096 : ℚ) := by
  norm_num [polynomial_119, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_119_00

def entry_119_00 : CachedQuarticSign :=
  ⟨polynomial_119, (619/4096 : ℚ), (837/4096 : ℚ),
    false, .leaf⟩

theorem entry_119_00_checked : entry_119_00.Check := by
  change polynomial_119.BernsteinNonnegCheck (619/4096 : ℚ) (837/4096 : ℚ)
  exact sign_119_00

def polynomial_120 : Quartic :=
  ⟨(133044167354938696606239011694757 : ℚ), (158878723984917092609405137520000 : ℚ), (-678311755326102556090925753890486 : ℚ), (172963439039082907390594862480000 : ℚ), (-73382504029061303393760988305243 : ℚ)⟩

theorem sign_120_00 :
    polynomial_120.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_120, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_120_00

def entry_120_00 : CachedQuarticSign :=
  ⟨polynomial_120, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_120_00_checked : entry_120_00.Check := by
  change polynomial_120.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_120_00

def polynomial_121 : Quartic :=
  ⟨(1362226778054100885248941849190329129633 : ℚ), (-2592482751598355766763206401793715259074 : ℚ), (-2530791578745288216000000000000000000000 : ℚ), (1333010484336296841236793598206284740926 : ℚ), (10581828097919862130751058150809670870367 : ℚ)⟩

theorem sign_121_00 :
    polynomial_121.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_121, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_121_00

def entry_121_00 : CachedQuarticSign :=
  ⟨polynomial_121, (75/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_121_00_checked : entry_121_00.Check := by
  change polynomial_121.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ)
  exact sign_121_00

def polynomial_122 : Quartic :=
  ⟨(139921815067023265734944459733519351 : ℚ), (-219126969764582217034742589968074838 : ℚ), (-5791113904062471416567956637665190982 : ℚ), (7156513139266182217034742589968074838 : ℚ), (-322185802595776734265055540266480649 : ℚ)⟩

theorem sign_122_00 :
    polynomial_122.BernsteinNonnegCheck (3675/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_122, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_122_00

def entry_122_00 : CachedQuarticSign :=
  ⟨polynomial_122, (3675/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_122_00_checked : entry_122_00.Check := by
  change polynomial_122.BernsteinNonnegCheck (3675/4096 : ℚ) (127/128 : ℚ)
  exact sign_122_00

def polynomial_123 : Quartic :=
  ⟨(1516051293895742302757427493233 : ℚ), (-3823232441309983647087685653406 : ℚ), (787821012208515394485145013534 : ℚ), (3823232441309983647087685653406 : ℚ), (-2303872306104257697242572506767 : ℚ)⟩

theorem sign_123_00 :
    polynomial_123.BernsteinNonnegCheck (619/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_123, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_123_00

def entry_123_00 : CachedQuarticSign :=
  ⟨polynomial_123, (619/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_123_00_checked : entry_123_00.Check := by
  change polynomial_123.BernsteinNonnegCheck (619/4096 : ℚ) (897/2048 : ℚ)
  exact sign_123_00

def polynomial_124 : Quartic :=
  ⟨(15190234105561662612219059402357 : ℚ), (363213935576000000000000000000000 : ℚ), (-18007764004876674775561881195286 : ℚ), (363213935576000000000000000000000 : ℚ), (-33197998110438337387780940597643 : ℚ)⟩

theorem sign_124_00 :
    polynomial_124.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_124, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_124_00

def entry_124_00 : CachedQuarticSign :=
  ⟨polynomial_124, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_124_00_checked : entry_124_00.Check := by
  change polynomial_124.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_124_00

def polynomial_125 : Quartic :=
  ⟨(157648495251749497778562646868894008628184529 : ℚ), (-590164939688597831063063054304344480277685282 : ℚ), (-128692054879523808015000000000000000000000000 : ℚ), (545115698516564487981736945695655519722314718 : ℚ), (837357166800793696332037353131105991371815471 : ℚ)⟩

theorem sign_125_00 :
    polynomial_125.BernsteinNonnegCheck (75/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_125, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_125_00

def entry_125_00 : CachedQuarticSign :=
  ⟨polynomial_125, (75/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_125_00_checked : entry_125_00.Check := by
  change polynomial_125.BernsteinNonnegCheck (75/4096 : ℚ) (309/2048 : ℚ)
  exact sign_125_00

def polynomial_126 : Quartic :=
  ⟨(160993 : ℚ), (1022484 : ℚ), (-160993 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_126_00 :
    polynomial_126.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_126, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_126_00

def entry_126_00 : CachedQuarticSign :=
  ⟨polynomial_126, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_126_00_checked : entry_126_00.Check := by
  change polynomial_126.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_126_00

def polynomial_127 : Quartic :=
  ⟨(163000353 : ℚ), (-1054067518 : ℚ), (-163000353 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_127_00 :
    polynomial_127.BernsteinNonnegCheck (75/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_127, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_127_00

def entry_127_00 : CachedQuarticSign :=
  ⟨polynomial_127, (75/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_127_00_checked : entry_127_00.Check := by
  change polynomial_127.BernsteinNonnegCheck (75/4096 : ℚ) (309/2048 : ℚ)
  exact sign_127_00

def cache : List CachedQuarticSign :=
  [entry_112_00, entry_113_00, entry_114_00, entry_115_00, entry_116_00, entry_117_00, entry_118_00, entry_119_00, entry_120_00, entry_121_00, entry_122_00, entry_123_00, entry_124_00, entry_125_00, entry_126_00, entry_127_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_112_00.Check ∧ entry_113_00.Check ∧ entry_114_00.Check ∧ entry_115_00.Check ∧ entry_116_00.Check ∧ entry_117_00.Check ∧ entry_118_00.Check ∧ entry_119_00.Check ∧ entry_120_00.Check ∧ entry_121_00.Check ∧ entry_122_00.Check ∧ entry_123_00.Check ∧ entry_124_00.Check ∧ entry_125_00.Check ∧ entry_126_00.Check ∧ entry_127_00.Check ∧ True
  exact ⟨entry_112_00_checked, entry_113_00_checked, entry_114_00_checked, entry_115_00_checked, entry_116_00_checked, entry_117_00_checked, entry_118_00_checked, entry_119_00_checked, entry_120_00_checked, entry_121_00_checked, entry_122_00_checked, entry_123_00_checked, entry_124_00_checked, entry_125_00_checked, entry_126_00_checked, entry_127_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk07
