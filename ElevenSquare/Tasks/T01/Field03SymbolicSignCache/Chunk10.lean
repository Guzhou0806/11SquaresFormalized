import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk10
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_159 : Quartic :=
  ⟨(263697290945007945959390768463319589 : ℚ), (-1043066085800229739199944362345289010 : ℚ), (403969895526526922712856970110756406 : ℚ), (2380990506776629739199944362345289010 : ℚ), (-1020245879677992054040609231536680411 : ℚ)⟩

theorem sign_159_00 :
    polynomial_159.BernsteinNonnegCheck (619/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_159, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_159_00

def entry_159_00 : CachedQuarticSign :=
  ⟨polynomial_159, (619/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_159_00_checked : entry_159_00.Check := by
  change polynomial_159.BernsteinNonnegCheck (619/4096 : ℚ) (897/2048 : ℚ)
  exact sign_159_00

def polynomial_160 : Quartic :=
  ⟨(26382293516631408741784568031197978451449041 : ℚ), (40439014728089481557528220731323621701768482 : ℚ), (23951758444329998404400000000000000000000000 : ℚ), (-92550182509591741988071779268676378298231518 : ℚ), (597304187512713453015431968802021548550959 : ℚ)⟩

theorem sign_160_00 :
    polynomial_160.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_160, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_160_00

def entry_160_00 : CachedQuarticSign :=
  ⟨polynomial_160, (1923/2048 : ℚ), (4069/4096 : ℚ),
    false, .leaf⟩

theorem entry_160_00_checked : entry_160_00.Check := by
  change polynomial_160.BernsteinNonnegCheck (1923/2048 : ℚ) (4069/4096 : ℚ)
  exact sign_160_00

def polynomial_161 : Quartic :=
  ⟨(264095 : ℚ), (-12063 : ℚ), (-264095 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_161_00 :
    polynomial_161.BernsteinPosCheck (1/4096 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_161, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_161_00

def entry_161_00 : CachedQuarticSign :=
  ⟨polynomial_161, (1/4096 : ℚ), (3863/4096 : ℚ),
    true, .leaf⟩

theorem entry_161_00_checked : entry_161_00.Check := by
  change polynomial_161.BernsteinPosCheck (1/4096 : ℚ) (3863/4096 : ℚ)
  exact sign_161_00

def polynomial_162 : Quartic :=
  ⟨(2741393064681555937500000000000000 : ℚ), (7981101483082250634548414178129466979 : ℚ), (-13296308534223696093750000000000000000 : ℚ), (3116765630293800634548414178129466979 : ℚ), (2429505176648269225312500000000000000 : ℚ)⟩

theorem sign_162_00 :
    polynomial_162.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_162, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_162_00

def entry_162_00 : CachedQuarticSign :=
  ⟨polynomial_162, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_162_00_checked : entry_162_00.Check := by
  change polynomial_162.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_162_00

def polynomial_163 : Quartic :=
  ⟨(274298525041314640760248899252154168307280857 : ℚ), (-1183693369957483355189019197220106101611194162 : ℚ), (-1542264097019043461963600000000000000000000000 : ℚ), (1086867906452841282900580802779893898388805838 : ℚ), (430832811803775901527351100747845831692719143 : ℚ)⟩

theorem sign_163_00 :
    polynomial_163.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ) := by
  norm_num [polynomial_163, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_163_00

def entry_163_00 : CachedQuarticSign :=
  ⟨polynomial_163, (1/4096 : ℚ), (5/128 : ℚ),
    false, .leaf⟩

theorem entry_163_00_checked : entry_163_00.Check := by
  change polynomial_163.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ)
  exact sign_163_00

def polynomial_164 : Quartic :=
  ⟨(278351680240000000000000000000 : ℚ), (243813505609289781925067472577 : ℚ), (-4339444008533875986761276945154 : ℚ), (7396110094390710218074932527423 : ℚ), (-3541610119760000000000000000000 : ℚ)⟩

theorem sign_164_00 :
    polynomial_164.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_164, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_164_00

def entry_164_00 : CachedQuarticSign :=
  ⟨polynomial_164, (247/512 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_164_00_checked : entry_164_00.Check := by
  change polynomial_164.BernsteinNonnegCheck (247/512 : ℚ) (2531/4096 : ℚ)
  exact sign_164_00

theorem sign_164_01 :
    polynomial_164.BernsteinNonnegCheck (633/1024 : ℚ) (3355/4096 : ℚ) := by
  norm_num [polynomial_164, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_164_01

def entry_164_01 : CachedQuarticSign :=
  ⟨polynomial_164, (633/1024 : ℚ), (3355/4096 : ℚ),
    false, .leaf⟩

theorem entry_164_01_checked : entry_164_01.Check := by
  change polynomial_164.BernsteinNonnegCheck (633/1024 : ℚ) (3355/4096 : ℚ)
  exact sign_164_01

def polynomial_165 : Quartic :=
  ⟨(279851668874719709111655701957350292 : ℚ), (-1157705131341864141677393784800378327 : ℚ), (437454275788293051276577880695101394 : ℚ), (2495629552318264141677393784800378327 : ℚ), (-1004091501748280290888344298042649708 : ℚ)⟩

theorem sign_165_00 :
    polynomial_165.BernsteinNonnegCheck (75/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_165, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_165_00

def entry_165_00 : CachedQuarticSign :=
  ⟨polynomial_165, (75/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_165_00_checked : entry_165_00.Check := by
  change polynomial_165.BernsteinNonnegCheck (75/4096 : ℚ) (309/2048 : ℚ)
  exact sign_165_00

theorem sign_165_01 :
    polynomial_165.BernsteinNonnegCheck (633/1024 : ℚ) (751/1024 : ℚ) := by
  norm_num [polynomial_165, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_165_01

def entry_165_01 : CachedQuarticSign :=
  ⟨polynomial_165, (633/1024 : ℚ), (751/1024 : ℚ),
    false, .leaf⟩

theorem entry_165_01_checked : entry_165_01.Check := by
  change polynomial_165.BernsteinNonnegCheck (633/1024 : ℚ) (751/1024 : ℚ)
  exact sign_165_01

def polynomial_166 : Quartic :=
  ⟨(29265944816686248571727062176126461771 : ℚ), (32261537340339735000000000000000000000 : ℚ), (-105629366912261383428272937823873538229 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_166_00 :
    polynomial_166.BernsteinNonnegCheck (1/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_166, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_166_00

def entry_166_00 : CachedQuarticSign :=
  ⟨polynomial_166, (1/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_166_00_checked : entry_166_00.Check := by
  change polynomial_166.BernsteinNonnegCheck (1/4096 : ℚ) (897/2048 : ℚ)
  exact sign_166_00

def polynomial_167 : Quartic :=
  ⟨(2968905988413062006619361527423 : ℚ), (-7237794094938579563850134945154 : ℚ), (1702035223173875986761276945154 : ℚ), (7237794094938579563850134945154 : ℚ), (-4670941211586937993380638472577 : ℚ)⟩

theorem sign_167_00 :
    polynomial_167.BernsteinNonnegCheck (161/4096 : ℚ) (1697/2048 : ℚ) := by
  norm_num [polynomial_167, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_167_00

def entry_167_00 : CachedQuarticSign :=
  ⟨polynomial_167, (161/4096 : ℚ), (1697/2048 : ℚ),
    false, .leaf⟩

theorem entry_167_00_checked : entry_167_00.Check := by
  change polynomial_167.BernsteinNonnegCheck (161/4096 : ℚ) (1697/2048 : ℚ)
  exact sign_167_00

theorem sign_167_01 :
    polynomial_167.BernsteinNonnegCheck (1663/2048 : ℚ) (3863/4096 : ℚ) := by
  norm_num [polynomial_167, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_167_01

def entry_167_01 : CachedQuarticSign :=
  ⟨polynomial_167, (1663/2048 : ℚ), (3863/4096 : ℚ),
    false, .leaf⟩

theorem entry_167_01_checked : entry_167_01.Check := by
  change polynomial_167.BernsteinNonnegCheck (1663/2048 : ℚ) (3863/4096 : ℚ)
  exact sign_167_01

def polynomial_168 : Quartic :=
  ⟨(298406254310000000000000000000 : ℚ), (152608530249289781925067472577 : ℚ), (-4379553156673875986761276945154 : ℚ), (7487315069750710218074932527423 : ℚ), (-3521555545690000000000000000000 : ℚ)⟩

theorem sign_168_00 :
    polynomial_168.BernsteinNonnegCheck (343/4096 : ℚ) (1001/2048 : ℚ) := by
  norm_num [polynomial_168, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_168_00

def entry_168_00 : CachedQuarticSign :=
  ⟨polynomial_168, (343/4096 : ℚ), (1001/2048 : ℚ),
    false, .leaf⟩

theorem entry_168_00_checked : entry_168_00.Check := by
  change polynomial_168.BernsteinNonnegCheck (343/4096 : ℚ) (1001/2048 : ℚ)
  exact sign_168_00

def polynomial_169 : Quartic :=
  ⟨(312468586286569842965531491986799093 : ℚ), (293739716508776670636867311684112547 : ℚ), (-1433590446226353445402822602232766572 : ℚ), (498533447711023329363132688315887453 : ℚ), (-180375091642730157034468508013200907 : ℚ)⟩

theorem sign_169_00 :
    polynomial_169.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_169, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_169_00

def entry_169_00 : CachedQuarticSign :=
  ⟨polynomial_169, (717/2048 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_169_00_checked : entry_169_00.Check := by
  change polynomial_169.BernsteinNonnegCheck (717/2048 : ℚ) (897/2048 : ℚ)
  exact sign_169_00

def polynomial_170 : Quartic :=
  ⟨(321400844081593350334125246525931321 : ℚ), (7476808937541899438366021616098987534 : ℚ), (-12117820957500228358927546092417879658 : ℚ), (2072809066278100561633978383901012466 : ℚ), (-326186983902806649665874753474068679 : ℚ)⟩

theorem sign_170_00 :
    polynomial_170.BernsteinNonnegCheck (1433/2048 : ℚ) (743/1024 : ℚ) := by
  norm_num [polynomial_170, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_170_00

def entry_170_00 : CachedQuarticSign :=
  ⟨polynomial_170, (1433/2048 : ℚ), (743/1024 : ℚ),
    false, .leaf⟩

theorem entry_170_00_checked : entry_170_00.Check := by
  change polynomial_170.BernsteinNonnegCheck (1433/2048 : ℚ) (743/1024 : ℚ)
  exact sign_170_00

def polynomial_171 : Quartic :=
  ⟨(321400844081593350334125246525931321 : ℚ), (8689838096202239918366021616098987534 : ℚ), (-10271242853658421318927546092417879658 : ℚ), (859779907617760081633978383901012466 : ℚ), (-326186983902806649665874753474068679 : ℚ)⟩

theorem sign_171_00 :
    polynomial_171.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_171, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_171_00

def entry_171_00 : CachedQuarticSign :=
  ⟨polynomial_171, (161/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_171_00_checked : entry_171_00.Check := by
  change polynomial_171.BernsteinNonnegCheck (161/4096 : ℚ) (309/2048 : ℚ)
  exact sign_171_00

def cache : List CachedQuarticSign :=
  [entry_159_00, entry_160_00, entry_161_00, entry_162_00, entry_163_00, entry_164_00, entry_164_01, entry_165_00, entry_165_01, entry_166_00, entry_167_00, entry_167_01, entry_168_00, entry_169_00, entry_170_00, entry_171_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_159_00.Check ∧ entry_160_00.Check ∧ entry_161_00.Check ∧ entry_162_00.Check ∧ entry_163_00.Check ∧ entry_164_00.Check ∧ entry_164_01.Check ∧ entry_165_00.Check ∧ entry_165_01.Check ∧ entry_166_00.Check ∧ entry_167_00.Check ∧ entry_167_01.Check ∧ entry_168_00.Check ∧ entry_169_00.Check ∧ entry_170_00.Check ∧ entry_171_00.Check ∧ True
  exact ⟨entry_159_00_checked, entry_160_00_checked, entry_161_00_checked, entry_162_00_checked, entry_163_00_checked, entry_164_00_checked, entry_164_01_checked, entry_165_00_checked, entry_165_01_checked, entry_166_00_checked, entry_167_00_checked, entry_167_01_checked, entry_168_00_checked, entry_169_00_checked, entry_170_00_checked, entry_171_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk10
