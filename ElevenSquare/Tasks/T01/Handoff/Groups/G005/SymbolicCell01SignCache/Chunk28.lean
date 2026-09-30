import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk28
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial336 : Quartic := ⟨7573059546805039844584763857491131340, 458328681943442386013959793499904346039, 4388815505537500800000000000000000000000, -8545448326945772693986040206500095653961, 4607388217649907640155415236142508868660⟩

theorem sign336 : polynomial336.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial336, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry336 : CachedQuarticSign :=
  ⟨polynomial336, 0, 1,
    false, .leaf⟩

theorem entry336_checked : entry336.Check := by
  change polynomial336.BernsteinNonnegCheck 0 1
  exact sign336

def polynomial337 : Quartic := ⟨769664820, -202932551, -1539329640, 202932551, 769664820⟩

theorem sign337 : polynomial337.BernsteinNonnegCheck (21/64) (19/32) := by
  norm_num [polynomial337, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry337 : CachedQuarticSign :=
  ⟨polynomial337, (21/64), (19/32),
    false, .leaf⟩

theorem entry337_checked : entry337.Check := by
  change polynomial337.BernsteinNonnegCheck (21/64) (19/32)
  exact sign337

def polynomial338 : Quartic := ⟨77435882068644256150049045771184731697402099, -741609782533912271264890156762760916037366720, -126872946384660280378915000000000000000000000, 520849845080909800480809843237239083962633280, 14750699634176308644515954228815268302597901⟩

theorem sign338 : polynomial338.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial338, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry338 : CachedQuarticSign :=
  ⟨polynomial338, 0, (1/64),
    false, .leaf⟩

theorem entry338_checked : entry338.Check := by
  change polynomial338.BernsteinNonnegCheck 0 (1/64)
  exact sign338

def polynomial339 : Quartic := ⟨78280164017708731893461558236848797, -202752588494012000000000000000000000, -49319306204490536213076883526302406, -202752588494012000000000000000000000, -127599470222199268106538441763151203⟩

theorem sign339 : polynomial339.BernsteinNonnegCheck (1/256) (1/64) := by
  norm_num [polynomial339, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry339 : CachedQuarticSign :=
  ⟨polynomial339, (1/256), (1/64),
    false, .leaf⟩

theorem entry339_checked : entry339.Check := by
  change polynomial339.BernsteinNonnegCheck (1/256) (1/64)
  exact sign339

def polynomial340 : Quartic := ⟨782852591249890240284920726706295555, -2043878350081396057693147694576007984, 300232475434956276416979335471272130, -2011173419798843942306852305423992016, -1275943751149189759715079273293704445⟩

theorem sign340 : polynomial340.BernsteinNonnegCheck (5/256) (11/64) := by
  norm_num [polynomial340, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry340 : CachedQuarticSign :=
  ⟨polynomial340, (5/256), (11/64),
    false, .leaf⟩

theorem entry340_checked : entry340.Check := by
  change polynomial340.BernsteinNonnegCheck (5/256) (11/64)
  exact sign340

def polynomial341 : Quartic := ⟨821213995805476958250445522431881779, 5677394653179370479378911714061534702, -66692222855287520000000000000000000000, 2084439719103610479378911714061534702, 11469649622418123041749554477568118221⟩

theorem sign341 : polynomial341.BernsteinNonnegCheck (5/256) (5/32) := by
  norm_num [polynomial341, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry341 : CachedQuarticSign :=
  ⟨polynomial341, (5/256), (5/32),
    false, .leaf⟩

theorem entry341_checked : entry341.Check := by
  change polynomial341.BernsteinNonnegCheck (5/256) (5/32)
  exact sign341

def polynomial342 : Quartic := ⟨82136247535775804792926896501047281729161104666701081, -63500478197911474590025908456848000000000000000000000, -18242222848787237146611643118872718270838895333298919, 0, 0⟩

theorem sign342 : polynomial342.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial342, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry342 : CachedQuarticSign :=
  ⟨polynomial342, 0, 1,
    false, .leaf⟩

theorem entry342_checked : entry342.Check := by
  change polynomial342.BernsteinNonnegCheck 0 1
  exact sign342

def polynomial343 : Quartic := ⟨827666667, 1528000000, -827666667, 0, 0⟩

theorem sign343 : polynomial343.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial343, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry343 : CachedQuarticSign :=
  ⟨polynomial343, 0, 1,
    false, .leaf⟩

theorem entry343_checked : entry343.Check := by
  change polynomial343.BernsteinNonnegCheck 0 1
  exact sign343

def polynomial344 : Quartic := ⟨833994277383860192392465474393825302101, 3259062441698386105147064275720529463280, 8918635274062753262048000000000000000000, -12554694613952439438468935724279470536720, 1497366293106777365399534525606174697899⟩

theorem sign344 : polynomial344.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial344, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry344 : CachedQuarticSign :=
  ⟨polynomial344, 0, 1,
    false, .leaf⟩

theorem entry344_checked : entry344.Check := by
  change polynomial344.BernsteinNonnegCheck 0 1
  exact sign344

def polynomial345 : Quartic := ⟨84899219417530521778029180423078363502332603, -501109412320275070321162051983739985017410733, -124915652733004170381400000000000000000000000, 1128455868891203132561037948016260014982589267, 285991175892149294313970819576921636497667397⟩

theorem sign345 : polynomial345.BernsteinNonnegCheck (7/64) (11/64) := by
  norm_num [polynomial345, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry345 : CachedQuarticSign :=
  ⟨polynomial345, (7/64), (11/64),
    false, .leaf⟩

theorem entry345_checked : entry345.Check := by
  change polynomial345.BernsteinNonnegCheck (7/64) (11/64)
  exact sign345

def polynomial346 : Quartic := ⟨849258905647478705167844899099916633, 2161646585280665388904000000000000000, -4761029415724823905928155100900083367, 0, 0⟩

theorem sign346 : polynomial346.BernsteinNonnegCheck 0 (25/64) := by
  norm_num [polynomial346, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry346 : CachedQuarticSign :=
  ⟨polynomial346, 0, (25/64),
    false, .leaf⟩

theorem entry346_checked : entry346.Check := by
  change polynomial346.BernsteinNonnegCheck 0 (25/64)
  exact sign346

def polynomial347 : Quartic := ⟨85238615, 225994534, -85238615, 0, 0⟩

theorem sign347 : polynomial347.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial347, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry347 : CachedQuarticSign :=
  ⟨polynomial347, 0, 1,
    false, .leaf⟩

theorem entry347_checked : entry347.Check := by
  change polynomial347.BernsteinNonnegCheck 0 1
  exact sign347

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk28
