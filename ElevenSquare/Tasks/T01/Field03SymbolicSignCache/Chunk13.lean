import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk13
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_202 : Quartic :=
  ⟨(514513 : ℚ), (787080 : ℚ), (-514513 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_202_00 :
    polynomial_202.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_202, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_202_00

def entry_202_00 : CachedQuarticSign :=
  ⟨polynomial_202, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_202_00_checked : entry_202_00.Check := by
  change polynomial_202.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_202_00

def polynomial_203 : Quartic :=
  ⟨(520457219973483028361849016302111623 : ℚ), (-2567886341246000000000000000000000000 : ℚ), (-297009981029433943276301967395776754 : ℚ), (-2567886341246000000000000000000000000 : ℚ), (-817467201002916971638150983697888377 : ℚ)⟩

theorem sign_203_00 :
    polynomial_203.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ) := by
  norm_num [polynomial_203, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_203_00

def entry_203_00 : CachedQuarticSign :=
  ⟨polynomial_203, (1/4096 : ℚ), (5/128 : ℚ),
    false, .leaf⟩

theorem entry_203_00_checked : entry_203_00.Check := by
  change polynomial_203.BernsteinNonnegCheck (1/4096 : ℚ) (5/128 : ℚ)
  exact sign_203_00

def polynomial_204 : Quartic :=
  ⟨(521520294727785970866449515920489522793930633 : ℚ), (-716775381357283565605792912195129507661861266 : ℚ), (-417822787525988338573680000000000000000000000 : ℚ), (362676111562918381402527087804870492338138734 : ℚ), (610045112275694564017150484079510477206069367 : ℚ)⟩

theorem sign_204_00 :
    polynomial_204.BernsteinNonnegCheck (1387/4096 : ℚ) (2531/4096 : ℚ) := by
  norm_num [polynomial_204, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_204_00

def entry_204_00 : CachedQuarticSign :=
  ⟨polynomial_204, (1387/4096 : ℚ), (2531/4096 : ℚ),
    false, .leaf⟩

theorem entry_204_00_checked : entry_204_00.Check := by
  change polynomial_204.BernsteinNonnegCheck (1387/4096 : ℚ) (2531/4096 : ℚ)
  exact sign_204_00

def polynomial_205 : Quartic :=
  ⟨(522667744730836803577694620468226259 : ℚ), (391644451126222874735955112715935840 : ℚ), (-2216355445310275607177915858173716274 : ℚ), (980273469966577125264044887284064160 : ℚ), (-153611529413163196422305379531773741 : ℚ)⟩

theorem sign_205_00 :
    polynomial_205.BernsteinNonnegCheck (633/1024 : ℚ) (2895/4096 : ℚ) := by
  norm_num [polynomial_205, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_205_00

def entry_205_00 : CachedQuarticSign :=
  ⟨polynomial_205, (633/1024 : ℚ), (2895/4096 : ℚ),
    false, .leaf⟩

theorem entry_205_00_checked : entry_205_00.Check := by
  change polynomial_205.BernsteinNonnegCheck (633/1024 : ℚ) (2895/4096 : ℚ)
  exact sign_205_00

def polynomial_206 : Quartic :=
  ⟨(524067 : ℚ), (-1406164 : ℚ), (-524067 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_206_00 :
    polynomial_206.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_206, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_206_00

def entry_206_00 : CachedQuarticSign :=
  ⟨polynomial_206, (75/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_206_00_checked : entry_206_00.Check := by
  change polynomial_206.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ)
  exact sign_206_00

def polynomial_207 : Quartic :=
  ⟨(527033759 : ℚ), (326000706 : ℚ), (-527033759 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_207_00 :
    polynomial_207.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_207, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_207_00

def entry_207_00 : CachedQuarticSign :=
  ⟨polynomial_207, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_207_00_checked : entry_207_00.Check := by
  change polynomial_207.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_207_00

def polynomial_208 : Quartic :=
  ⟨(52830516524257028703656919328751983339318031 : ℚ), (22918820751089669238462302531474445202509154 : ℚ), (-469002939866896274029200000000000000000000000 : ℚ), (-57144173095485521202337697468525554797490846 : ℚ), (108161427676229835917543080671248016660681969 : ℚ)⟩

theorem sign_208_00 :
    polynomial_208.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ) := by
  norm_num [polynomial_208, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_208_00

def entry_208_00 : CachedQuarticSign :=
  ⟨polynomial_208, (1/4096 : ℚ), (309/2048 : ℚ),
    false, .leaf⟩

theorem entry_208_00_checked : entry_208_00.Check := by
  change polynomial_208.BernsteinNonnegCheck (1/4096 : ℚ) (309/2048 : ℚ)
  exact sign_208_00

def polynomial_209 : Quartic :=
  ⟨(530531 : ℚ), (-523246 : ℚ), (-530531 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_209_00 :
    polynomial_209.BernsteinNonnegCheck (647/2048 : ℚ) (1119/2048 : ℚ) := by
  norm_num [polynomial_209, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_209_00

def entry_209_00 : CachedQuarticSign :=
  ⟨polynomial_209, (647/2048 : ℚ), (1119/2048 : ℚ),
    false, .leaf⟩

theorem entry_209_00_checked : entry_209_00.Check := by
  change polynomial_209.BernsteinNonnegCheck (647/2048 : ℚ) (1119/2048 : ℚ)
  exact sign_209_00

def polynomial_210 : Quartic :=
  ⟨(540223 : ℚ), (-1419504 : ℚ), (-540223 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_210_00 :
    polynomial_210.BernsteinNonnegCheck (1/4096 : ℚ) (1293/4096 : ℚ) := by
  norm_num [polynomial_210, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_210_00

def entry_210_00 : CachedQuarticSign :=
  ⟨polynomial_210, (1/4096 : ℚ), (1293/4096 : ℚ),
    false, .leaf⟩

theorem entry_210_00_checked : entry_210_00.Check := by
  change polynomial_210.BernsteinNonnegCheck (1/4096 : ℚ) (1293/4096 : ℚ)
  exact sign_210_00

def polynomial_211 : Quartic :=
  ⟨(5439137946031939848234 : ℚ), (-9813971168888210531181 : ℚ), (-878475892063879696468 : ℚ), (9813971168888210531181 : ℚ), (-4560662053968060151766 : ℚ)⟩

theorem sign_211_00 :
    polynomial_211.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_211, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_211_00

def entry_211_00 : CachedQuarticSign :=
  ⟨polynomial_211, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_211_00_checked : entry_211_00.Check := by
  change polynomial_211.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_211_00

def polynomial_212 : Quartic :=
  ⟨(563546 : ℚ), (511932824 : ℚ), (-344888451 : ℚ), (488057176 : ℚ), (-499431454 : ℚ)⟩

theorem sign_212_00 :
    polynomial_212.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_212, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_212_00

def entry_212_00 : CachedQuarticSign :=
  ⟨polynomial_212, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_212_00_checked : entry_212_00.Check := by
  change polynomial_212.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_212_00

def polynomial_213 : Quartic :=
  ⟨(61467335647711841662452606528614626359 : ℚ), (17623786734425270879640951983451394944 : ℚ), (-268567135891303954364905844993334548042 : ℚ), (260133049777739529120359048016548605056 : ℚ), (-66658226869786558337547393471385373641 : ℚ)⟩

theorem sign_213_00 :
    polynomial_213.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_213, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_213_00

def entry_213_00 : CachedQuarticSign :=
  ⟨polynomial_213, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_213_00_checked : entry_213_00.Check := by
  change polynomial_213.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_213_00

def polynomial_214 : Quartic :=
  ⟨(618971 : ℚ), (528160 : ℚ), (-618971 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_214_00 :
    polynomial_214.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_214, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_214_00

def entry_214_00 : CachedQuarticSign :=
  ⟨polynomial_214, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_214_00_checked : entry_214_00.Check := by
  change polynomial_214.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_214_00

def polynomial_215 : Quartic :=
  ⟨(66549673006503155017547393471385373641 : ℚ), (18565870765140143240359048016548605056 : ℚ), (-254386699569741921475094155006665451958 : ℚ), (259190965747024656759640951983451394944 : ℚ), (-61575889510995244982452606528614626359 : ℚ)⟩

theorem sign_215_00 :
    polynomial_215.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_215, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_215_00

def entry_215_00 : CachedQuarticSign :=
  ⟨polynomial_215, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_215_00_checked : entry_215_00.Check := by
  change polynomial_215.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_215_00

def polynomial_216 : Quartic :=
  ⟨(6805772402225347481936321887725396101649 : ℚ), (-8246111081991082568834855593917905021348 : ℚ), (11845426420893316800000000000000000000000 : ℚ), (-8246111081991082568834855593917905021348 : ℚ), (5039654018667969318063678112274603898351 : ℚ)⟩

theorem sign_216_00 :
    polynomial_216.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_216, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_216_00

def entry_216_00 : CachedQuarticSign :=
  ⟨polynomial_216, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_216_00_checked : entry_216_00.Check := by
  change polynomial_216.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_216_00

def polynomial_217 : Quartic :=
  ⟨(70479984810170631418485151876172896328004143 : ℚ), (1889585606931786845771259030237967637772975838 : ℚ), (-2457196882054311912971800000000000000000000000 : ℚ), (3389703908021851922847259030237967637772975838 : ℚ), (263064622606078322225714848123827103671995857 : ℚ)⟩

theorem sign_217_00 :
    polynomial_217.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_217, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_217_00

def entry_217_00 : CachedQuarticSign :=
  ⟨polynomial_217, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_217_00_checked : entry_217_00.Check := by
  change polynomial_217.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_217_00

def cache : List CachedQuarticSign :=
  [entry_202_00, entry_203_00, entry_204_00, entry_205_00, entry_206_00, entry_207_00, entry_208_00, entry_209_00, entry_210_00, entry_211_00, entry_212_00, entry_213_00, entry_214_00, entry_215_00, entry_216_00, entry_217_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_202_00.Check ∧ entry_203_00.Check ∧ entry_204_00.Check ∧ entry_205_00.Check ∧ entry_206_00.Check ∧ entry_207_00.Check ∧ entry_208_00.Check ∧ entry_209_00.Check ∧ entry_210_00.Check ∧ entry_211_00.Check ∧ entry_212_00.Check ∧ entry_213_00.Check ∧ entry_214_00.Check ∧ entry_215_00.Check ∧ entry_216_00.Check ∧ entry_217_00.Check ∧ True
  exact ⟨entry_202_00_checked, entry_203_00_checked, entry_204_00_checked, entry_205_00_checked, entry_206_00_checked, entry_207_00_checked, entry_208_00_checked, entry_209_00_checked, entry_210_00_checked, entry_211_00_checked, entry_212_00_checked, entry_213_00_checked, entry_214_00_checked, entry_215_00_checked, entry_216_00_checked, entry_217_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk13
