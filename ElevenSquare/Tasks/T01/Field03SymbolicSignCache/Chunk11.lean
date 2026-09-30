import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk11
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_172 : Quartic :=
  ⟨(338306158004508657681859278870373641 : ℚ), (4686347937961375315094786942770747282 : ℚ), (-138882369630542800000000000000000000000 : ℚ), (260937257911542175315094786942770747282 : ℚ), (138541500910036691342318140721129626359 : ℚ)⟩

theorem sign_172_00 :
    polynomial_172.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ) := by
  norm_num [polynomial_172, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_172_00

def entry_172_00 : CachedQuarticSign :=
  ⟨polynomial_172, (1/4096 : ℚ), (315/4096 : ℚ),
    false, .leaf⟩

theorem entry_172_00_checked : entry_172_00.Check := by
  change polynomial_172.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ)
  exact sign_172_00

def polynomial_173 : Quartic :=
  ⟨(3423465911493385330693021496829 : ℚ), (1753722980445072201094369985000 : ℚ), (-13704145321298077142535300896342 : ℚ), (7224797445554927798905630015000 : ℚ), (-1002445568506614669306978503171 : ℚ)⟩

theorem sign_173_00 :
    polynomial_173.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_173, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_173_00

def entry_173_00 : CachedQuarticSign :=
  ⟨polynomial_173, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_173_00_checked : entry_173_00.Check := by
  change polynomial_173.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_173_00

def polynomial_174 : Quartic :=
  ⟨(3433676183968060151766 : ℚ), (-9021226061111789468819 : ℚ), (3132447632063879696468 : ℚ), (9021226061111789468819 : ℚ), (-6566123816031939848234 : ℚ)⟩

theorem sign_174_00 :
    polynomial_174.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_174, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_174_00

def entry_174_00 : CachedQuarticSign :=
  ⟨polynomial_174, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_174_00_checked : entry_174_00.Check := by
  change polynomial_174.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_174_00

def polynomial_175 : Quartic :=
  ⟨(3434069843812134333050127031 : ℚ), (1438935613384280000000000000 : ℚ), (28152754139400000000000000000 : ℚ), (-725687181398615720000000000000 : ℚ), (695532584749987865666949872969 : ℚ)⟩

theorem sign_175_00 :
    polynomial_175.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ) := by
  norm_num [polynomial_175, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_175_00

def entry_175_00 : CachedQuarticSign :=
  ⟨polynomial_175, (1/4096 : ℚ), (315/4096 : ℚ),
    false, .leaf⟩

theorem entry_175_00_checked : entry_175_00.Check := by
  change polynomial_175.BernsteinNonnegCheck (1/4096 : ℚ) (315/4096 : ℚ)
  exact sign_175_00

def polynomial_176 : Quartic :=
  ⟨(34707298980679458296969276330363 : ℚ), (497742276738572800000000000000000 : ℚ), (-499995678016000000000000000000000 : ℚ), (633365476738572800000000000000000 : ℚ), (465277023003320541703030723669637 : ℚ)⟩

theorem sign_176_00 :
    polynomial_176.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_176, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_176_00

def entry_176_00 : CachedQuarticSign :=
  ⟨polynomial_176, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_176_00_checked : entry_176_00.Check := by
  change polynomial_176.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_176_00

def polynomial_177 : Quartic :=
  ⟨(351541 : ℚ), (524067 : ℚ), (-351541 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_177_00 :
    polynomial_177.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_177, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_177_00

def entry_177_00 : CachedQuarticSign :=
  ⟨polynomial_177, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_177_00_checked : entry_177_00.Check := by
  change polynomial_177.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_177_00

def polynomial_178 : Quartic :=
  ⟨(354876 : ℚ), (540223 : ℚ), (-354876 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_178_00 :
    polynomial_178.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_178, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_178_00

def entry_178_00 : CachedQuarticSign :=
  ⟨polynomial_178, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_178_00_checked : entry_178_00.Check := by
  change polynomial_178.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_178_00

def polynomial_179 : Quartic :=
  ⟨(36598096235742302757427493233 : ℚ), (3371812900550016352912314346594 : ℚ), (-73196192471484605514854986466 : ℚ), (-3371812900550016352912314346594 : ℚ), (36598096235742302757427493233 : ℚ)⟩

theorem sign_179_00 :
    polynomial_179.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_179, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_179_00

def entry_179_00 : CachedQuarticSign :=
  ⟨polynomial_179, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_179_00_checked : entry_179_00.Check := by
  change polynomial_179.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_179_00

def polynomial_180 : Quartic :=
  ⟨(369444245481755487938543799418791899 : ℚ), (-136764724650800000000000000000000000 : ℚ), (-198634594199769024122912401162416202 : ℚ), (-136764724650800000000000000000000000 : ℚ), (-568078839681524512061456200581208101 : ℚ)⟩

theorem sign_180_00 :
    polynomial_180.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ) := by
  norm_num [polynomial_180, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_180_00

def entry_180_00 : CachedQuarticSign :=
  ⟨polynomial_180, (633/1024 : ℚ), (1423/2048 : ℚ),
    false, .leaf⟩

theorem entry_180_00_checked : entry_180_00.Check := by
  change polynomial_180.BernsteinNonnegCheck (633/1024 : ℚ) (1423/2048 : ℚ)
  exact sign_180_00

def polynomial_181 : Quartic :=
  ⟨(37751452090588131570515300195539405766963 : ℚ), (-21578148068702836716568165856266036173926 : ℚ), (-119834695885651049928000000000000000000000 : ℚ), (-31654647862013889964568165856266036173926 : ℚ), (446625581594950269093484699804460594233037 : ℚ)⟩

theorem sign_181_00 :
    polynomial_181.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_181, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_181_00

def entry_181_00 : CachedQuarticSign :=
  ⟨polynomial_181, (75/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_181_00_checked : entry_181_00.Check := by
  change polynomial_181.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ)
  exact sign_181_00

def polynomial_182 : Quartic :=
  ⟨(3809924006906937993380638472577 : ℚ), (-7152296588781420436149865054846 : ℚ), (19999186186124013238723054846 : ℚ), (7152296588781420436149865054846 : ℚ), (-3829923193093062006619361527423 : ℚ)⟩

theorem sign_182_00 :
    polynomial_182.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_182, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_182_00

def entry_182_00 : CachedQuarticSign :=
  ⟨polynomial_182, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_182_00_checked : entry_182_00.Check := by
  change polynomial_182.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_182_00

def polynomial_183 : Quartic :=
  ⟨(3823450363533062006619361527423 : ℚ), (-7237794094938579563850134945154 : ℚ), (-7053527066124013238723054846 : ℚ), (7237794094938579563850134945154 : ℚ), (-3816396836466937993380638472577 : ℚ)⟩

theorem sign_183_00 :
    polynomial_183.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_183, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_183_00

def entry_183_00 : CachedQuarticSign :=
  ⟨polynomial_183, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_183_00_checked : entry_183_00.Check := by
  change polynomial_183.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_183_00

def polynomial_184 : Quartic :=
  ⟨(3889828034850974947576153539 : ℚ), (-98067231411222775516958399098 : ℚ), (258595219021950000000000000000 : ℚ), (-83992672158222775516958399098 : ℚ), (-94779754126500974947576153539 : ℚ)⟩

theorem sign_184_00 :
    polynomial_184.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_184, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_184_00

def entry_184_00 : CachedQuarticSign :=
  ⟨polynomial_184, (1795/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_184_00_checked : entry_184_00.Check := by
  change polynomial_184.BernsteinNonnegCheck (1795/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_184_00

def polynomial_185 : Quartic :=
  ⟨(3891134108212460668950000000 : ℚ), (1873382803764257697242572506767 : ℚ), (-5274011532333591431574414346594 : ℚ), (1946578996235742302757427493233 : ℚ), (-1906089765891787539331050000000 : ℚ)⟩

theorem sign_185_00 :
    polynomial_185.BernsteinNonnegCheck (1387/4096 : ℚ) (1605/4096 : ℚ) := by
  norm_num [polynomial_185, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_185_00

def entry_185_00 : CachedQuarticSign :=
  ⟨polynomial_185, (1387/4096 : ℚ), (1605/4096 : ℚ),
    false, .leaf⟩

theorem entry_185_00_checked : entry_185_00.Check := by
  change polynomial_185.BernsteinNonnegCheck (1387/4096 : ℚ) (1605/4096 : ℚ)
  exact sign_185_00

def polynomial_186 : Quartic :=
  ⟨(397237555704111111 : ℚ), (1191712664884000000 : ℚ), (-2383425334224666666 : ℚ), (-1191712664884000000 : ℚ), (397237555704111111 : ℚ)⟩

theorem sign_186_00 :
    polynomial_186.BernsteinNonnegCheck (1795/4096 : ℚ) (1119/2048 : ℚ) := by
  norm_num [polynomial_186, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_186_00

def entry_186_00 : CachedQuarticSign :=
  ⟨polynomial_186, (1795/4096 : ℚ), (1119/2048 : ℚ),
    false, .leaf⟩

theorem entry_186_00_checked : entry_186_00.Check := by
  change polynomial_186.BernsteinNonnegCheck (1795/4096 : ℚ) (1119/2048 : ℚ)
  exact sign_186_00

def polynomial_187 : Quartic :=
  ⟨(407448597718582269 : ℚ), (452836800000000000 : ℚ), (199998000000000000000 : ℚ), (-399547163200000000000 : ℚ), (199590551402281417731 : ℚ)⟩

theorem sign_187_00 :
    polynomial_187.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_187, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_187_00

def entry_187_00 : CachedQuarticSign :=
  ⟨polynomial_187, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_187_00_checked : entry_187_00.Check := by
  change polynomial_187.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_187_00

def cache : List CachedQuarticSign :=
  [entry_172_00, entry_173_00, entry_174_00, entry_175_00, entry_176_00, entry_177_00, entry_178_00, entry_179_00, entry_180_00, entry_181_00, entry_182_00, entry_183_00, entry_184_00, entry_185_00, entry_186_00, entry_187_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_172_00.Check ∧ entry_173_00.Check ∧ entry_174_00.Check ∧ entry_175_00.Check ∧ entry_176_00.Check ∧ entry_177_00.Check ∧ entry_178_00.Check ∧ entry_179_00.Check ∧ entry_180_00.Check ∧ entry_181_00.Check ∧ entry_182_00.Check ∧ entry_183_00.Check ∧ entry_184_00.Check ∧ entry_185_00.Check ∧ entry_186_00.Check ∧ entry_187_00.Check ∧ True
  exact ⟨entry_172_00_checked, entry_173_00_checked, entry_174_00_checked, entry_175_00_checked, entry_176_00_checked, entry_177_00_checked, entry_178_00_checked, entry_179_00_checked, entry_180_00_checked, entry_181_00_checked, entry_182_00_checked, entry_183_00_checked, entry_184_00_checked, entry_185_00_checked, entry_186_00_checked, entry_187_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk11
