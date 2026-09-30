import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_016 : Quartic :=
  ⟨(-15653753942314040442786977890377665 : ℚ), (136929911343202068315006947840294362 : ℚ), (-96020275203924089140495747495246086 : ℚ), (-18840793172802068315006947840294362 : ℚ), (14344106088485959557213022109622335 : ℚ)⟩

theorem sign_016_00 :
    polynomial_016.BernsteinNonnegCheck (2973/4096 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_016, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_016_00

def entry_016_00 : CachedQuarticSign :=
  ⟨polynomial_016, (2973/4096 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_016_00_checked : entry_016_00.Check := by
  change polynomial_016.BernsteinNonnegCheck (2973/4096 : ℚ) (3863/4096 : ℚ)
  exact sign_016_00

def polynomial_017 : Quartic :=
  ⟨(-15653753942314040442786977890377665 : ℚ), (143427866771614548315006947840294362 : ℚ), (-56181416435829689140495747495246086 : ℚ), (-25338748601214548315006947840294362 : ℚ), (14344106088485959557213022109622335 : ℚ)⟩

theorem sign_017_00 :
    polynomial_017.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_017, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_017_00

def entry_017_00 : CachedQuarticSign :=
  ⟨polynomial_017, (1923/2048 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_017_00_checked : entry_017_00.Check := by
  change polynomial_017.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_017_00

def polynomial_018 : Quartic :=
  ⟨(-16182774312091915576677320616535908 : ℚ), (-19255320349357490294272142605037845 : ℚ), (246066744610215450574418261803139758 : ℚ), (-159007781117306509705727857394962155 : ℚ), (-194445875578759915576677320616535908 : ℚ)⟩

theorem sign_018_00 :
    polynomial_018.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_018, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_018_00

def entry_018_00 : CachedQuarticSign :=
  ⟨polynomial_018, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_018_00_checked : entry_018_00.Check := by
  change polynomial_018.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_018_00

def polynomial_019 : Quartic :=
  ⟨(-163000353 : ℚ), (1054067518 : ℚ), (163000353 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_019_00 :
    polynomial_019.BernsteinNonnegCheck (619/4096 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_019, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_019_00

def entry_019_00 : CachedQuarticSign :=
  ⟨polynomial_019, (619/4096 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_019_00_checked : entry_019_00.Check := by
  change polynomial_019.BernsteinNonnegCheck (619/4096 : ℚ) (4069/4096 : ℚ)
  exact sign_019_00

def polynomial_020 : Quartic :=
  ⟨(-16588226711119076575703572569913490859 : ℚ), (-6793130339523629147451234420810724981718 : ℚ), (13619437140146641200000000000000000000000 : ℚ), (16588219089806052548765579189275018282 : ℚ), (-6793130339542239723424296427430086509141 : ℚ)⟩

theorem sign_020_00 :
    polynomial_020.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_020, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_020_00

def entry_020_00 : CachedQuarticSign :=
  ⟨polynomial_020, (633/1024 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_020_00_checked : entry_020_00.Check := by
  change polynomial_020.BernsteinNonnegCheck (633/1024 : ℚ) (3863/4096 : ℚ)
  exact sign_020_00

def polynomial_021 : Quartic :=
  ⟨(-16622442614221579451505356249218087 : ℚ), (1189699289596963773374863596959004916 : ℚ), (-87881842944914221141511895524618270 : ℚ), (1078067114167836226625136403040995084 : ℚ), (-215395987063821579451505356249218087 : ℚ)⟩

theorem sign_021_00 :
    polynomial_021.BernsteinNonnegCheck (619/4096 : ℚ) (1195/4096 : ℚ) := by
  norm_num [polynomial_021, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_021_00

def entry_021_00 : CachedQuarticSign :=
  ⟨polynomial_021, (619/4096 : ℚ), (1195/4096 : ℚ),
    false, .leaf⟩

theorem entry_021_00_checked : entry_021_00.Check := by
  change polynomial_021.BernsteinNonnegCheck (619/4096 : ℚ) (1195/4096 : ℚ)
  exact sign_021_00

def polynomial_022 : Quartic :=
  ⟨(-1702587534573860318870284384179743049640871089 : ℚ), (1103770506825484269662343621641566484393807074 : ℚ), (3457830704303058773904400000000000000000000000 : ℚ), (-1896466095354645884489656378358433515606192926 : ℚ), (-421064740064202640457315615820256950359128911 : ℚ)⟩

theorem sign_022_00 :
    polynomial_022.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_022, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_022_00

def entry_022_00 : CachedQuarticSign :=
  ⟨polynomial_022, (2847/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_022_00_checked : entry_022_00.Check := by
  change polynomial_022.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ)
  exact sign_022_00

def polynomial_023 : Quartic :=
  ⟨(-174947159954454944388775128000000 : ℚ), (169329843206062739875283333934757 : ℚ), (-20255061776000000000000000000000 : ℚ), (3405443206062739875283333934757 : ℚ), (361122898178454944388775128000000 : ℚ)⟩

theorem sign_023_00 :
    polynomial_023.BernsteinNonnegCheck (3301/4096 : ℚ) (1837/2048 : ℚ) := by
  norm_num [polynomial_023, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_023_00

def entry_023_00 : CachedQuarticSign :=
  ⟨polynomial_023, (3301/4096 : ℚ), (1837/2048 : ℚ),
    false, .leaf⟩

theorem entry_023_00_checked : entry_023_00.Check := by
  change polynomial_023.BernsteinNonnegCheck (3301/4096 : ℚ) (1837/2048 : ℚ)
  exact sign_023_00

def polynomial_024 : Quartic :=
  ⟨(-175306880089248879029857775917 : ℚ), (4136346984812311925462957289794 : ℚ), (350613760178497758059715551834 : ℚ), (-4136346984812311925462957289794 : ℚ), (-175306880089248879029857775917 : ℚ)⟩

theorem sign_024_00 :
    polynomial_024.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_024, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_024_00

def entry_024_00 : CachedQuarticSign :=
  ⟨polynomial_024, (717/2048 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_024_00_checked : entry_024_00.Check := by
  change polynomial_024.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ)
  exact sign_024_00

def polynomial_025 : Quartic :=
  ⟨(-178343964522787865666949872969 : ℚ), (336846167334584280000000000000 : ℚ), (391708822872600000000000000000 : ℚ), (-1061094413119815720000000000000 : ℚ), (513754550383387865666949872969 : ℚ)⟩

theorem sign_025_00 :
    polynomial_025.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_025, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_025_00

def entry_025_00 : CachedQuarticSign :=
  ⟨polynomial_025, (1923/2048 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_025_00_checked : entry_025_00.Check := by
  change polynomial_025.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_025_00

def polynomial_026 : Quartic :=
  ⟨(-18178167 : ℚ), (33541394 : ℚ), (18178167 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_026_00 :
    polynomial_026.BernsteinPosCheck (1795/4096 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_026, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_026_00

def entry_026_00 : CachedQuarticSign :=
  ⟨polynomial_026, (1795/4096 : ℚ), (4069/4096 : ℚ),
    true, .leaf⟩

theorem entry_026_00_checked : entry_026_00.Check := by
  change polynomial_026.BernsteinPosCheck (1795/4096 : ℚ) (4069/4096 : ℚ)
  exact sign_026_00

def polynomial_027 : Quartic :=
  ⟨(-185076824167327711846890401389946949194402919 : ℚ), (978746351442701058277697798504308336614561714 : ℚ), (1828829053777157544413200000000000000000000000 : ℚ), (-1291814924967623579811902201495691663385438286 : ℚ), (-233489555919648747991109598610053050805597081 : ℚ)⟩

theorem sign_027_00 :
    polynomial_027.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_027, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_027_00

def entry_027_00 : CachedQuarticSign :=
  ⟨polynomial_027, (2847/4096 : ℚ), (127/128 : ℚ),
    false, .leaf⟩

theorem entry_027_00_checked : entry_027_00.Check := by
  change polynomial_027.BernsteinNonnegCheck (2847/4096 : ℚ) (127/128 : ℚ)
  exact sign_027_00

def polynomial_028 : Quartic :=
  ⟨(-1869058212324257697242572506767 : ℚ), (7282979675910016352912314346594 : ℚ), (-2708143958111484605514854986466 : ℚ), (356943924089983647087685653406 : ℚ), (-1869096412324257697242572506767 : ℚ)⟩

theorem sign_028_00 :
    polynomial_028.BernsteinNonnegCheck (1387/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_028, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_028_00

def entry_028_00 : CachedQuarticSign :=
  ⟨polynomial_028, (1387/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_028_00_checked : entry_028_00.Check := by
  change polynomial_028.BernsteinNonnegCheck (1387/4096 : ℚ) (897/2048 : ℚ)
  exact sign_028_00

def polynomial_029 : Quartic :=
  ⟨(-1922185450735092979004299795492676818110943 : ℚ), (6420393948686183444049903597801653889026626 : ℚ), (5621898148268220400200000000000000000000000 : ℚ), (-4894281200486972513950096402198346110973374 : ℚ), (-1095090059363040715595700204507323181889057 : ℚ)⟩

theorem sign_029_00 :
    polynomial_029.BernsteinNonnegCheck (131/512 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_029, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_029_00

def entry_029_00 : CachedQuarticSign :=
  ⟨polynomial_029, (131/512 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_029_00_checked : entry_029_00.Check := by
  change polynomial_029.BernsteinNonnegCheck (131/512 : ℚ) (1293/4096 : ℚ)
  exact sign_029_00

def polynomial_030 : Quartic :=
  ⟨(-196770 : ℚ), (514513 : ℚ), (196770 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_030_00 :
    polynomial_030.BernsteinPosCheck (1387/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_030, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_030_00

def entry_030_00 : CachedQuarticSign :=
  ⟨polynomial_030, (1387/4096 : ℚ), (127/128 : ℚ),
    true, .leaf⟩

theorem entry_030_00_checked : entry_030_00.Check := by
  change polynomial_030.BernsteinPosCheck (1387/4096 : ℚ) (127/128 : ℚ)
  exact sign_030_00

def polynomial_031 : Quartic :=
  ⟨(-218002520027538515229680944030723678389 : ℚ), (-171494376185401605238965268542288386124 : ℚ), (3845411346392257747260620324143867484582 : ℚ), (-3233330861827880794761034731457711613876 : ℚ), (-3622827754220897315229680944030723678389 : ℚ)⟩

theorem sign_031_00 :
    polynomial_031.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_031, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_031_00

def entry_031_00 : CachedQuarticSign :=
  ⟨polynomial_031, (717/2048 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_031_00_checked : entry_031_00.Check := by
  change polynomial_031.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ)
  exact sign_031_00

def cache : List CachedQuarticSign :=
  [entry_016_00, entry_017_00, entry_018_00, entry_019_00, entry_020_00, entry_021_00, entry_022_00, entry_023_00, entry_024_00, entry_025_00, entry_026_00, entry_027_00, entry_028_00, entry_029_00, entry_030_00, entry_031_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_016_00.Check ∧ entry_017_00.Check ∧ entry_018_00.Check ∧ entry_019_00.Check ∧ entry_020_00.Check ∧ entry_021_00.Check ∧ entry_022_00.Check ∧ entry_023_00.Check ∧ entry_024_00.Check ∧ entry_025_00.Check ∧ entry_026_00.Check ∧ entry_027_00.Check ∧ entry_028_00.Check ∧ entry_029_00.Check ∧ entry_030_00.Check ∧ entry_031_00.Check ∧ True
  exact ⟨entry_016_00_checked, entry_017_00_checked, entry_018_00_checked, entry_019_00_checked, entry_020_00_checked, entry_021_00_checked, entry_022_00_checked, entry_023_00_checked, entry_024_00_checked, entry_025_00_checked, entry_026_00_checked, entry_027_00_checked, entry_028_00_checked, entry_029_00_checked, entry_030_00_checked, entry_031_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk01
