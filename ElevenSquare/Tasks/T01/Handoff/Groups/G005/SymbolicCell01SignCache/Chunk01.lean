import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial012 : Quartic := ⟨-1211324591, 1081785010, 1211324591, 0, 0⟩

theorem sign012 : polynomial012.BernsteinNonnegCheck (11/16) 1 := by
  norm_num [polynomial012, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry012 : CachedQuarticSign :=
  ⟨polynomial012, (11/16), 1,
    false, .leaf⟩

theorem entry012_checked : entry012.Check := by
  change polynomial012.BernsteinNonnegCheck (11/16) 1
  exact sign012

def polynomial013 : Quartic := ⟨-1224101629263767034859509505622697704016315, 27828941149239110971940341160148082234588509, -18931513612834434125228000000000000000000000, -28705510969714178860727658839851917765411491, 3541439000433475327419509505622697704016315⟩

theorem sign013 : polynomial013.BernsteinNonnegCheck (7/32) (1/4) := by
  norm_num [polynomial013, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry013 : CachedQuarticSign :=
  ⟨polynomial013, (7/32), (1/4),
    false, .leaf⟩

theorem entry013_checked : entry013.Check := by
  change polynomial013.BernsteinNonnegCheck (7/32) (1/4)
  exact sign013

def polynomial014 : Quartic := ⟨-12529696476422868782949573643443552941, 651221716153962800000000000000000000000, 850767696805337371217050426356556447059, 0, 0⟩

theorem sign014 : polynomial014.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial014, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry014 : CachedQuarticSign :=
  ⟨polynomial014, (1/2), (19/32),
    false, .leaf⟩

theorem entry014_checked : entry014.Check := by
  change polynomial014.BernsteinNonnegCheck (1/2) (19/32)
  exact sign014

def polynomial015 : Quartic := ⟨-127330281502211613519479676934327341476826209, 687953221485449267234267028734479307004224599, -611757389312671620205440000000000000000000000, -814439046917526485721452971265520692995775401, -167874516407869004766000323065672658523173791⟩

theorem sign015 : polynomial015.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial015, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry015 : CachedQuarticSign :=
  ⟨polynomial015, (19/64), (5/16),
    false, .leaf⟩

theorem entry015_checked : entry015.Check := by
  change polynomial015.BernsteinNonnegCheck (19/64) (5/16)
  exact sign015

def polynomial016 : Quartic := ⟨-127654259751299524232161735143041890, 257535643908881308728165343311763607, 20206134988662987000000000000000000000, -20719581533771145691271834656688236393, 384648322756979524232161735143041890⟩

theorem sign016 : polynomial016.BernsteinNonnegCheck (5/64) (11/64) := by
  norm_num [polynomial016, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry016 : CachedQuarticSign :=
  ⟨polynomial016, (5/64), (11/64),
    false, .leaf⟩

theorem entry016_checked : entry016.Check := by
  change polynomial016.BernsteinNonnegCheck (5/64) (11/64)
  exact sign016

def polynomial017 : Quartic := ⟨-128072997153436017850916791394000000, 282488599835779445749285152100634151, 20206134988662987000000000000000000000, -20694628577844247554250714847899365849, 385067060159116017850916791394000000⟩

theorem sign017 : polynomial017.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial017, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry017 : CachedQuarticSign :=
  ⟨polynomial017, (11/16), (27/32),
    false, .leaf⟩

theorem entry017_checked : entry017.Check := by
  change polynomial017.BernsteinNonnegCheck (11/16) (27/32)
  exact sign017

def polynomial018 : Quartic := ⟨-130248760911478918529459831437669674877565044, 329592062449432166169140399000851927155638887, 197698410313935202906748000000000000000000000, -272120446705212061692075600999148072844361113, -188505236583006167960352168562330325122434956⟩

theorem sign018 : polynomial018.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial018, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry018 : CachedQuarticSign :=
  ⟨polynomial018, (101/256), (19/32),
    false, .leaf⟩

theorem entry018_checked : entry018.Check := by
  change polynomial018.BernsteinNonnegCheck (101/256) (19/32)
  exact sign018

def polynomial019 : Quartic := ⟨-133504084680104033022419699472281781623251891, 276859958688510108430145000000000000000000000, 340256568247763042341625300527718218376748109, 0, 0⟩

theorem sign019 : polynomial019.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial019, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry019 : CachedQuarticSign :=
  ⟨polynomial019, (101/256), (19/32),
    false, .leaf⟩

theorem entry019_checked : entry019.Check := by
  change polynomial019.BernsteinNonnegCheck (101/256) (19/32)
  exact sign019

def polynomial020 : Quartic := ⟨-137255305054707613974732159203626272, 1217423968589122397732264722464109487, 2677374949517824584403861382636146444, 163850888855637602267735277535890513, -1495745818068247613974732159203626272⟩

theorem sign020 : polynomial020.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial020, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry020 : CachedQuarticSign :=
  ⟨polynomial020, (19/64), (5/16),
    false, .leaf⟩

theorem entry020_checked : entry020.Check := by
  change polynomial020.BernsteinNonnegCheck (19/64) (5/16)
  exact sign020

def polynomial021 : Quartic := ⟨-1381990889058500060935702060215741, 2344013314392890344510534916758926601, 1847971798177141598647101885616031910, -2991612799191330344510534916758926601, -2388829465984558500060935702060215741⟩

theorem sign021 : polynomial021.BernsteinNonnegCheck (11/16) (23/32) := by
  norm_num [polynomial021, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry021 : CachedQuarticSign :=
  ⟨polynomial021, (11/16), (23/32),
    false, .leaf⟩

theorem entry021_checked : entry021.Check := by
  change polynomial021.BernsteinNonnegCheck (11/16) (23/32)
  exact sign021

def polynomial022 : Quartic := ⟨-13847517558936501147899412876047476175500000, 2937067711300990494843917876440157447202471, 45807726997795440634665000000000000000000000, 1116902562222706826568917876440157447202471, -18408234110681136352100587123952523824500000⟩

theorem sign022 : polynomial022.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial022, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry022 : CachedQuarticSign :=
  ⟨polynomial022, (11/16), (27/32),
    false, .leaf⟩

theorem entry022_checked : entry022.Check := by
  change polynomial022.BernsteinNonnegCheck (11/16) (27/32)
  exact sign022

def polynomial023 : Quartic := ⟨-140527852913449416775718577384000000, 294113131887153107265845980577724403, 20206134988662987000000000000000000000, -20683004045792873892734154019422275597, 397521915919129416775718577384000000⟩

theorem sign023 : polynomial023.BernsteinNonnegCheck (61/128) (19/32) := by
  norm_num [polynomial023, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry023 : CachedQuarticSign :=
  ⟨polynomial023, (61/128), (19/32),
    false, .leaf⟩

theorem entry023_checked : entry023.Check := by
  change polynomial023.BernsteinNonnegCheck (61/128) (19/32)
  exact sign023

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk01
