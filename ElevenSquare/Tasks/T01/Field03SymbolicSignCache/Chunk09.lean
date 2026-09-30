import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk09
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_143 : Quartic :=
  ⟨(1901 : ℚ), (11655 : ℚ), (-1901 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_143_00 :
    polynomial_143.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_143, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_143_00

def entry_143_00 : CachedQuarticSign :=
  ⟨polynomial_143, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_143_00_checked : entry_143_00.Check := by
  change polynomial_143.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_143_00

def polynomial_144 : Quartic :=
  ⟨(19576516163434828402853637408320647188773 : ℚ), (-18186185388812178372489776440934237916746 : ℚ), (16850615255774503600000000000000000000000 : ℚ), (-18186185388812178372489776440934237916746 : ℚ), (-2725900907660324802853637408320647188773 : ℚ)⟩

theorem sign_144_00 :
    polynomial_144.BernsteinNonnegCheck (1663/2048 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_144, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_144_00

def entry_144_00 : CachedQuarticSign :=
  ⟨polynomial_144, (1663/2048 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_144_00_checked : entry_144_00.Check := by
  change polynomial_144.BernsteinNonnegCheck (1663/2048 : ℚ) (3863/4096 : ℚ)
  exact sign_144_00

def polynomial_145 : Quartic :=
  ⟨(196770 : ℚ), (-514513 : ℚ), (-196770 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_145_00 :
    polynomial_145.BernsteinNonnegCheck (1/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_145, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_145_00

def entry_145_00 : CachedQuarticSign :=
  ⟨polynomial_145, (1/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_145_00_checked : entry_145_00.Check := by
  change polynomial_145.BernsteinNonnegCheck (1/4096 : ℚ) (679/2048 : ℚ)
  exact sign_145_00

def polynomial_146 : Quartic :=
  ⟨(1974321 : ℚ), (2351647 : ℚ), (999990000 : ℚ), (-1997648353 : ℚ), (998015679 : ℚ)⟩

theorem sign_146_00 :
    polynomial_146.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_146, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_146_00

def entry_146_00 : CachedQuarticSign :=
  ⟨polynomial_146, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_146_00_checked : entry_146_00.Check := by
  change polynomial_146.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_146_00

def polynomial_147 : Quartic :=
  ⟨(19785108033297922919116052780192953 : ℚ), (1660760413649446683197229118864034606 : ℚ), (-63202901680400000000000000000000000 : ℚ), (-6398285946350553316802770881135965394 : ℚ), (8102301710286302077080883947219807047 : ℚ)⟩

theorem sign_147_00 :
    polynomial_147.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_147, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_147_00

def entry_147_00 : CachedQuarticSign :=
  ⟨polynomial_147, (1/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_147_00_checked : entry_147_00.Check := by
  change polynomial_147.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ)
  exact sign_147_00

def polynomial_148 : Quartic :=
  ⟨(2007958570864505493831315012022274726943 : ℚ), (-2527463840610338579683171398407364906752 : ℚ), (-2321113491191520929530313953729074175162 : ℚ), (5018059421542461779683171398407364906752 : ℚ), (-2018498817137119306168684987977725273057 : ℚ)⟩

theorem sign_148_00 :
    polynomial_148.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_148, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_148_00

def entry_148_00 : CachedQuarticSign :=
  ⟨polynomial_148, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_148_00_checked : entry_148_00.Check := by
  change polynomial_148.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_148_00

def polynomial_149 : Quartic :=
  ⟨(2017113841305287857500631379193375458498291 : ℚ), (-4999613732574747276325538976382587592629862 : ℚ), (-23159371713894640142960000000000000000000000 : ℚ), (2498078348060439204954461023617412407370138 : ℚ), (2470471173313841852659368620806624541501709 : ℚ)⟩

theorem sign_149_00 :
    polynomial_149.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ) := by
  norm_num [polynomial_149, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_149_00

def entry_149_00 : CachedQuarticSign :=
  ⟨polynomial_149, (1/4096 : ℚ), (5/128 : ℚ),
    false, .leaf⟩

theorem entry_149_00_checked : entry_149_00.Check := by
  change polynomial_149.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ)
  exact sign_149_00

def polynomial_150 : Quartic :=
  ⟨(204884666003640000000000000 : ℚ), (185438071841810455666949872969 : ℚ), (-153634369310700000000000000000 : ℚ), (-178118278385389544333050127031 : ℚ), (181574967517296360000000000000 : ℚ)⟩

theorem sign_150_00 :
    polynomial_150.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_150, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_150_00

def entry_150_00 : CachedQuarticSign :=
  ⟨polynomial_150, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_150_00_checked : entry_150_00.Check := by
  change polynomial_150.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_150_00

def polynomial_151 : Quartic :=
  ⟨(208186348066768428852336085640343750 : ℚ), (-5007901076914010306863652056517730833 : ℚ), (36321506056463498437500000000000000000 : ℚ), (-26735927715099804056863652056517730833 : ℚ), (-5072679487492669991352336085640343750 : ℚ)⟩

theorem sign_151_00 :
    polynomial_151.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_151, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_151_00

def entry_151_00 : CachedQuarticSign :=
  ⟨polynomial_151, (65/128 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_151_00_checked : entry_151_00.Check := by
  change polynomial_151.BernsteinNonnegCheck (65/128 : ℚ) (2531/4096 : ℚ)
  exact sign_151_00

def polynomial_152 : Quartic :=
  ⟨(2236272885000000000000000000 : ℚ), (1516070393895742302757427493233 : ℚ), (-5728740795539983647087685653406 : ℚ), (2303891406104257697242572506767 : ℚ), (-1907744627115000000000000000000 : ℚ)⟩

theorem sign_152_00 :
    polynomial_152.BernsteinNonnegCheck (619/4096 : ℚ) (1195/4096 : ℚ) := by
  norm_num [polynomial_152, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_152_00

def entry_152_00 : CachedQuarticSign :=
  ⟨polynomial_152, (619/4096 : ℚ), (1195/4096 : ℚ),
    false, .leaf⟩

theorem entry_152_00_checked : entry_152_00.Check := by
  change polynomial_152.BernsteinNonnegCheck (619/4096 : ℚ) (1195/4096 : ℚ)
  exact sign_152_00

def polynomial_153 : Quartic :=
  ⟨(228770856130276817884793632255774033 : ℚ), (-643675008918878273886482323969732606 : ℚ), (1133901204358200000000000000000000000 : ℚ), (-842452528918878273886482323969732606 : ℚ), (-228775531772076817884793632255774033 : ℚ)⟩

theorem sign_153_00 :
    polynomial_153.BernsteinNonnegCheck (647/2048 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_153, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_153_00

def entry_153_00 : CachedQuarticSign :=
  ⟨polynomial_153, (647/2048 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_153_00_checked : entry_153_00.Check := by
  change polynomial_153.BernsteinNonnegCheck (647/2048 : ℚ) (897/2048 : ℚ)
  exact sign_153_00

def polynomial_154 : Quartic :=
  ⟨(231950434541668009631091721052590752084370541 : ℚ), (-216619609812171848504599172513335024266741082 : ℚ), (-5173953700010402179494800000000000000000000000 : ℚ), (-312850182838292407022999172513335024266741082 : ℚ), (364317882852789064027708278947409247915629459 : ℚ)⟩

theorem sign_154_00 :
    polynomial_154.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ) := by
  norm_num [polynomial_154, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_154_00

def entry_154_00 : CachedQuarticSign :=
  ⟨polynomial_154, (1/4096 : ℚ), (5/128 : ℚ),
    false, .leaf⟩

theorem entry_154_00_checked : entry_154_00.Check := by
  change polynomial_154.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ)
  exact sign_154_00

def polynomial_155 : Quartic :=
  ⟨(232722 : ℚ), (-50633 : ℚ), (-232722 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_155_00 :
    polynomial_155.BernsteinPosCheck (75/4096 : ℚ) (1837/2048 : ℚ) := by
  norm_num [polynomial_155, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_155_00

def entry_155_00 : CachedQuarticSign :=
  ⟨polynomial_155, (75/4096 : ℚ), (1837/2048 : ℚ),
    true, .leaf⟩

theorem entry_155_00_checked : entry_155_00.Check := by
  change polynomial_155.BernsteinPosCheck (75/4096 : ℚ) (1837/2048 : ℚ)
  exact sign_155_00

def polynomial_156 : Quartic :=
  ⟨(255621 : ℚ), (-160993 : ℚ), (-255621 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_156_00 :
    polynomial_156.BernsteinPosCheck (1/4096 : ℚ) (751/1024 : ℚ) := by
  norm_num [polynomial_156, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_156_00

def entry_156_00 : CachedQuarticSign :=
  ⟨polynomial_156, (1/4096 : ℚ), (751/1024 : ℚ),
    true, .leaf⟩

theorem entry_156_00_checked : entry_156_00.Check := by
  change polynomial_156.BernsteinPosCheck (1/4096 : ℚ) (751/1024 : ℚ)
  exact sign_156_00

def polynomial_157 : Quartic :=
  ⟨(261293837319712171072447015127809389 : ℚ), (207349514552475994836397345794658464 : ℚ), (-1180966514702830544187259258812403662 : ℚ), (478609445993924005163602654205341536 : ℚ), (-76845799752287828927552984872190611 : ℚ)⟩

theorem sign_157_00 :
    polynomial_157.BernsteinNonnegCheck (131/512 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_157, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_157_00

def entry_157_00 : CachedQuarticSign :=
  ⟨polynomial_157, (131/512 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_157_00_checked : entry_157_00.Check := by
  change polynomial_157.BernsteinNonnegCheck (131/512 : ℚ) (897/2048 : ℚ)
  exact sign_157_00

def polynomial_158 : Quartic :=
  ⟨(261623 : ℚ), (1061062 : ℚ), (-261623 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_158_00 :
    polynomial_158.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_158, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_158_00

def entry_158_00 : CachedQuarticSign :=
  ⟨polynomial_158, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_158_00_checked : entry_158_00.Check := by
  change polynomial_158.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_158_00

def cache : List CachedQuarticSign :=
  [entry_143_00, entry_144_00, entry_145_00, entry_146_00, entry_147_00, entry_148_00, entry_149_00, entry_150_00, entry_151_00, entry_152_00, entry_153_00, entry_154_00, entry_155_00, entry_156_00, entry_157_00, entry_158_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_143_00.Check ∧ entry_144_00.Check ∧ entry_145_00.Check ∧ entry_146_00.Check ∧ entry_147_00.Check ∧ entry_148_00.Check ∧ entry_149_00.Check ∧ entry_150_00.Check ∧ entry_151_00.Check ∧ entry_152_00.Check ∧ entry_153_00.Check ∧ entry_154_00.Check ∧ entry_155_00.Check ∧ entry_156_00.Check ∧ entry_157_00.Check ∧ entry_158_00.Check ∧ True
  exact ⟨entry_143_00_checked, entry_144_00_checked, entry_145_00_checked, entry_146_00_checked, entry_147_00_checked, entry_148_00_checked, entry_149_00_checked, entry_150_00_checked, entry_151_00_checked, entry_152_00_checked, entry_153_00_checked, entry_154_00_checked, entry_155_00_checked, entry_156_00_checked, entry_157_00_checked, entry_158_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk09
