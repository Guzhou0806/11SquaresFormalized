import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk02
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_032 : Quartic :=
  ⟨(-226789536247830896755828152770306209219 : ℚ), (1549724657231805609939639125859628882182 : ℚ), (776309772060188676800000000000000000000 : ℚ), (-1406475223471276726060360874140371117818 : ℚ), (951608588884124751155828152770306209219 : ℚ)⟩

theorem sign_032_00 :
    polynomial_032.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_032, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_032_00

def entry_032_00 : CachedQuarticSign :=
  ⟨polynomial_032, (619/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_032_00_checked : entry_032_00.Check := by
  change polynomial_032.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ)
  exact sign_032_00

def polynomial_033 : Quartic :=
  ⟨(-2277942656223467856735914178129466979 : ℚ), (34452910541589890256875000000000000000 : ℚ), (-36321506056463498437500000000000000000 : ℚ), (56180937179775684006875000000000000000 : ℚ), (7142435795649369419235914178129466979 : ℚ)⟩

theorem sign_033_00 :
    polynomial_033.BernsteinNonnegCheck (343/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_033, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_033_00

def entry_033_00 : CachedQuarticSign :=
  ⟨polynomial_033, (343/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_033_00_checked : entry_033_00.Check := by
  change polynomial_033.BernsteinNonnegCheck (343/4096 : ℚ) (309/2048 : ℚ)
  exact sign_033_00

def polynomial_034 : Quartic :=
  ⟨(-232722 : ℚ), (50633 : ℚ), (232722 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_034_00 :
    polynomial_034.BernsteinNonnegCheck (3675/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_034, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_034_00

def entry_034_00 : CachedQuarticSign :=
  ⟨polynomial_034, (3675/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_034_00_checked : entry_034_00.Check := by
  change polynomial_034.BernsteinNonnegCheck (3675/4096 : ℚ) (127/128 : ℚ)
  exact sign_034_00

def polynomial_035 : Quartic :=
  ⟨(-2543580225140388129382190237037538492271 : ℚ), (6614369140461550000000000000000000000000 : ℚ), (-3703143032617213996382190237037538492271 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_035_00 :
    polynomial_035.BernsteinNonnegCheck (633/1024 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_035, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_035_00

def entry_035_00 : CachedQuarticSign :=
  ⟨polynomial_035, (633/1024 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_035_00_checked : entry_035_00.Check := by
  change polynomial_035.BernsteinNonnegCheck (633/1024 : ℚ) (4069/4096 : ℚ)
  exact sign_035_00

def polynomial_036 : Quartic :=
  ⟨(-255621 : ℚ), (160993 : ℚ), (255621 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_036_00 :
    polynomial_036.BernsteinNonnegCheck (3005/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_036, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_036_00

def entry_036_00 : CachedQuarticSign :=
  ⟨polynomial_036, (3005/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_036_00_checked : entry_036_00.Check := by
  change polynomial_036.BernsteinNonnegCheck (3005/4096 : ℚ) (127/128 : ℚ)
  exact sign_036_00

def polynomial_037 : Quartic :=
  ⟨(-258085911272858909059266128123827103671995857 : ℚ), (2468707204191217469097600000000000000000000000 : ℚ), (-2064848225803993771338066128123827103671995857 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_037_00 :
    polynomial_037.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_037, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_037_00

def entry_037_00 : CachedQuarticSign :=
  ⟨polynomial_037, (619/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_037_00_checked : entry_037_00.Check := by
  change polynomial_037.BernsteinNonnegCheck (619/4096 : ℚ) (679/2048 : ℚ)
  exact sign_037_00

def polynomial_038 : Quartic :=
  ⟨(-26357679254407434928272937823873538229 : ℚ), (134895311728947632000000000000000000000 : ℚ), (-50005742841167699928272937823873538229 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_038_00 :
    polynomial_038.BernsteinNonnegCheck (1795/4096 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_038, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_038_00

def entry_038_00 : CachedQuarticSign :=
  ⟨polynomial_038, (1795/4096 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_038_00_checked : entry_038_00.Check := by
  change polynomial_038.BernsteinNonnegCheck (1795/4096 : ℚ) (4069/4096 : ℚ)
  exact sign_038_00

def polynomial_039 : Quartic :=
  ⟨(-2799371900823216706584977360526191 : ℚ), (566941600941200000000000000000000000 : ℚ), (-104985516026446433413169954721052382 : ℚ), (566941600941200000000000000000000000 : ℚ), (-102186144125623216706584977360526191 : ℚ)⟩

theorem sign_039_00 :
    polynomial_039.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_039, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_039_00

def entry_039_00 : CachedQuarticSign :=
  ⟨polynomial_039, (161/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_039_00_checked : entry_039_00.Check := by
  change polynomial_039.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ)
  exact sign_039_00

def polynomial_040 : Quartic :=
  ⟨(-28016905828388224047142492781464079176378537 : ℚ), (190609734163980077399318750000000000000000000 : ℚ), (-105288767287944125732861242781464079176378537 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_040_00 :
    polynomial_040.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_040, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_040_00

def entry_040_00 : CachedQuarticSign :=
  ⟨polynomial_040, (677/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_040_00_checked : entry_040_00.Check := by
  change polynomial_040.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ)
  exact sign_040_00

def polynomial_041 : Quartic :=
  ⟨(-29412800516792280193666084421115419 : ℚ), (59044559085200000000000000000000000 : ℚ), (-28827741002784560387332168842230838 : ℚ), (59044559085200000000000000000000000 : ℚ), (585059514007719806333915578884581 : ℚ)⟩

theorem sign_041_00 :
    polynomial_041.BernsteinNonnegCheck (633/1024 : ℚ) (743/1024 : ℚ) := by
  norm_num [polynomial_041, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_041_00

def entry_041_00 : CachedQuarticSign :=
  ⟨polynomial_041, (633/1024 : ℚ), (743/1024 : ℚ),
    false, .leaf⟩

theorem entry_041_00_checked : entry_041_00.Check := by
  change polynomial_041.BernsteinNonnegCheck (633/1024 : ℚ) (743/1024 : ℚ)
  exact sign_041_00

def polynomial_042 : Quartic :=
  ⟨(-30074334954690752014506725559193401 : ℚ), (-1157416858775754556715646400242643840 : ℚ), (71737352402369673782537337405039160406 : ℚ), (-126968145658722645443284353599757356160 : ℚ), (-69469283462995890752014506725559193401 : ℚ)⟩

theorem sign_042_00 :
    polynomial_042.BernsteinNonnegCheck (619/4096 : ℚ) (811/4096 : ℚ) := by
  norm_num [polynomial_042, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_042_00

def entry_042_00 : CachedQuarticSign :=
  ⟨polynomial_042, (619/4096 : ℚ), (811/4096 : ℚ),
    false, .leaf⟩

theorem entry_042_00_checked : entry_042_00.Check := by
  change polynomial_042.BernsteinNonnegCheck (619/4096 : ℚ) (811/4096 : ℚ)
  exact sign_042_00

def polynomial_043 : Quartic :=
  ⟨(-3033530453142425569844265604568180319 : ℚ), (-1225693440068554895822630024044549453886 : ℚ), (9298305550454655600000000000000000000000 : ℚ), (-6788068259444118095822630024044549453886 : ℚ), (-1242276713239888374430155734395431819681 : ℚ)⟩

theorem sign_043_00 :
    polynomial_043.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_043, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_043_00

def entry_043_00 : CachedQuarticSign :=
  ⟨polynomial_043, (633/1024 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_043_00_checked : entry_043_00.Check := by
  change polynomial_043.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ)
  exact sign_043_00

def polynomial_044 : Quartic :=
  ⟨(-31712700180016838518187379165026698265336961 : ℚ), (77171403035587204761748707934964713387953278 : ℚ), (62275858468196654462800000000000000000000000 : ℚ), (-104919072926311030135851292065035286612046722 : ℚ), (-53499555862249792020612620834973301734663039 : ℚ)⟩

theorem sign_044_00 :
    polynomial_044.BernsteinNonnegCheck (633/1024 : ℚ) (751/1024 : ℚ) := by
  norm_num [polynomial_044, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_044_00

def entry_044_00 : CachedQuarticSign :=
  ⟨polynomial_044, (633/1024 : ℚ), (751/1024 : ℚ),
    false, .leaf⟩

theorem entry_044_00_checked : entry_044_00.Check := by
  change polynomial_044.BernsteinNonnegCheck (633/1024 : ℚ) (751/1024 : ℚ)
  exact sign_044_00

def polynomial_045 : Quartic :=
  ⟨(-3230509441756387220102696275628413871 : ℚ), (4092563007102800000000000000000000000 : ℚ), (-2431576293976374440205392551256827742 : ℚ), (4092563007102800000000000000000000000 : ℚ), (798933147780012779897303724371586129 : ℚ)⟩

theorem sign_045_00 :
    polynomial_045.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_045, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_045_00

def entry_045_00 : CachedQuarticSign :=
  ⟨polynomial_045, (2847/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_045_00_checked : entry_045_00.Check := by
  change polynomial_045.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ)
  exact sign_045_00

def polynomial_046 : Quartic :=
  ⟨(-324076241228161993810253616072192258460577077 : ℚ), (3014855808232937740485740878508513205227154154 : ℚ), (878661113774749810064400000000000000000000000 : ℚ), (-2421400521884473008331859121491486794772845846 : ℚ), (-472440062981729734413346383927807741539422923 : ℚ)⟩

theorem sign_046_00 :
    polynomial_046.BernsteinNonnegCheck (619/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_046, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_046_00

def entry_046_00 : CachedQuarticSign :=
  ⟨polynomial_046, (619/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_046_00_checked : entry_046_00.Check := by
  change polynomial_046.BernsteinNonnegCheck (619/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_046_00

def polynomial_047 : Quartic :=
  ⟨(-329297970682923309755303543902435246169069367 : ℚ), (451200928912192380353459031840979045587861266 : ℚ), (713742618266439661845040000000000000000000000 : ℚ), (-628250564008009566654860968159020954412138734 : ℚ), (-506347605580105901856936456097564753830930633 : ℚ)⟩

theorem sign_047_00 :
    polynomial_047.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ) := by
  norm_num [polynomial_047, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_047_00

def entry_047_00 : CachedQuarticSign :=
  ⟨polynomial_047, (633/1024 : ℚ), (1423/2048 : ℚ),
    false, .leaf⟩

theorem entry_047_00_checked : entry_047_00.Check := by
  change polynomial_047.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ)
  exact sign_047_00

def cache : List CachedQuarticSign :=
  [entry_032_00, entry_033_00, entry_034_00, entry_035_00, entry_036_00, entry_037_00, entry_038_00, entry_039_00, entry_040_00, entry_041_00, entry_042_00, entry_043_00, entry_044_00, entry_045_00, entry_046_00, entry_047_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_032_00.Check ∧ entry_033_00.Check ∧ entry_034_00.Check ∧ entry_035_00.Check ∧ entry_036_00.Check ∧ entry_037_00.Check ∧ entry_038_00.Check ∧ entry_039_00.Check ∧ entry_040_00.Check ∧ entry_041_00.Check ∧ entry_042_00.Check ∧ entry_043_00.Check ∧ entry_044_00.Check ∧ entry_045_00.Check ∧ entry_046_00.Check ∧ entry_047_00.Check ∧ True
  exact ⟨entry_032_00_checked, entry_033_00_checked, entry_034_00_checked, entry_035_00_checked, entry_036_00_checked, entry_037_00_checked, entry_038_00_checked, entry_039_00_checked, entry_040_00_checked, entry_041_00_checked, entry_042_00_checked, entry_043_00_checked, entry_044_00_checked, entry_045_00_checked, entry_046_00_checked, entry_047_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk02
