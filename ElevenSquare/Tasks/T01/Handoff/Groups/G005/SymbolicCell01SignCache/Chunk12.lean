import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk12
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial144 : Quartic := ⟨105372407659149132854144902299066063159653595, -288941212021113750670124967309104793591049122, -4941553401471732303397000000000000000000000000, -6512987681644877747471164967309104793591049122, 3846648981040566850542855097700933936840346405⟩

theorem sign144 : polynomial144.BernsteinNonnegCheck (5/256) (3/32) := by
  norm_num [polynomial144, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry144 : CachedQuarticSign :=
  ⟨polynomial144, (5/256), (3/32),
    false, .leaf⟩

theorem entry144_checked : entry144.Check := by
  change polynomial144.BernsteinNonnegCheck (5/256) (3/32)
  exact sign144

def polynomial145 : Quartic := ⟨107427575470645311305200000, -221312970153898558995375389, 0, -221312970153898558995375389, -107427575470645311305200000⟩

theorem sign145 : polynomial145.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial145, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry145 : CachedQuarticSign :=
  ⟨polynomial145, (91/256), (25/64),
    false, .leaf⟩

theorem entry145_checked : entry145.Check := by
  change polynomial145.BernsteinNonnegCheck (91/256) (25/64)
  exact sign145

def polynomial146 : Quartic := ⟨10779721051858736302618577495418537710636043, 55455203512979402336744672728415405406504564, -1875694590323217540198040000000000000000000000, -4478727111209250867670295327271584594593495436, 1205226861188414247094381422504581462289363957⟩

theorem sign146 : polynomial146.BernsteinNonnegCheck (5/256) (7/128) := by
  norm_num [polynomial146, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry146 : CachedQuarticSign :=
  ⟨polynomial146, (5/256), (7/128),
    false, .leaf⟩

theorem entry146_checked : entry146.Check := by
  change polynomial146.BernsteinNonnegCheck (5/256) (7/128)
  exact sign146

def polynomial147 : Quartic := ⟨1092262848439195101586523586410735490859, 1439674180760913544781947235352542000000, -7304584352409345853495132965297677018282, 6342923582252429975218052764647458000000, -853386596134133138413476413589264509141⟩

theorem sign147 : polynomial147.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial147, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry147 : CachedQuarticSign :=
  ⟨polynomial147, 0, 1,
    false, .leaf⟩

theorem entry147_checked : entry147.Check := by
  change polynomial147.BernsteinNonnegCheck 0 1
  exact sign147

def polynomial148 : Quartic := ⟨1104856986474204115311363431615897220563120195, 14759348866280717664670625064827436370014849, -1641876935836260996599620000000000000000000000, -1532654797789510561786809374935172563629985151, 496132224545897264833856568384102779436879805⟩

theorem sign148 : polynomial148.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial148, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry148 : CachedQuarticSign :=
  ⟨polynomial148, (101/256), (19/32),
    false, .leaf⟩

theorem entry148_checked : entry148.Check := by
  change polynomial148.BernsteinNonnegCheck (101/256) (19/32)
  exact sign148

def polynomial149 : Quartic := ⟨112997267, -170477230, -112997267, 0, 0⟩

theorem sign149 : polynomial149.BernsteinNonnegCheck (91/256) (31/64) := by
  norm_num [polynomial149, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry149 : CachedQuarticSign :=
  ⟨polynomial149, (91/256), (31/64),
    false, .leaf⟩

theorem entry149_checked : entry149.Check := by
  change polynomial149.BernsteinNonnegCheck (91/256) (31/64)
  exact sign149

def polynomial150 : Quartic := ⟨1138338611126466236689755436207312922511, 24160837640657647779101867765716763262490, 26059597472039284523065600000000000000000, -41056204124530543635717172234283236737510, 9348604552345258963310244563792687077489⟩

theorem sign150 : polynomial150.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial150, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry150 : CachedQuarticSign :=
  ⟨polynomial150, 0, 1,
    false, .leaf⟩

theorem entry150_checked : entry150.Check := by
  change polynomial150.BernsteinNonnegCheck 0 1
  exact sign150

def polynomial151 : Quartic := ⟨11457890552374671058345778296691918530000, 196140381054361189962600972185448139073957, 59634117173326316401600000000000000000000, -167722498907179032526199027814551860926043, -22259339079989209948745778296691918530000⟩

theorem sign151 : polynomial151.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial151, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry151 : CachedQuarticSign :=
  ⟨polynomial151, 0, 1,
    false, .leaf⟩

theorem entry151_checked : entry151.Check := by
  change polynomial151.BernsteinNonnegCheck 0 1
  exact sign151

def polynomial152 : Quartic := ⟨116965307802678409104214182354, 552078152432981570588469740, -1755022266785116057655961837285, 3819444101847567018429411530260, -1793032782197321590895785817646⟩

theorem sign152 : polynomial152.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial152, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry152 : CachedQuarticSign :=
  ⟨polynomial152, (11/16), (27/32),
    false, .leaf⟩

theorem entry152_checked : entry152.Check := by
  change polynomial152.BernsteinNonnegCheck (11/16) (27/32)
  exact sign152

def polynomial153 : Quartic := ⟨1178505993, -59202880, -1178505993, 0, 0⟩

theorem sign153 : polynomial153.BernsteinNonnegCheck (91/256) (499/512) := by
  norm_num [polynomial153, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry153 : CachedQuarticSign :=
  ⟨polynomial153, (91/256), (499/512),
    false, .leaf⟩

theorem entry153_checked : entry153.Check := by
  change polynomial153.BernsteinNonnegCheck (91/256) (499/512)
  exact sign153

def polynomial154 : Quartic := ⟨1181518391248498694237824225417979067331, 1662037893581757262905218436326839473376, -8021729267832069457816578261143557423866, 6120559869431586257094781563673160526624, -764131053324829545762175774582020932669⟩

theorem sign154 : polynomial154.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial154, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry154 : CachedQuarticSign :=
  ⟨polynomial154, (1/2), (19/32),
    false, .leaf⟩

theorem entry154_checked : entry154.Check := by
  change polynomial154.BernsteinNonnegCheck (1/2) (19/32)
  exact sign154

def polynomial155 : Quartic := ⟨12070112061274126021948967515230869788681, 24018336689325953703200000000000000000000, -91532264659653427681251032484769130211319, 0, 0⟩

theorem sign155 : polynomial155.BernsteinNonnegCheck 0 (11/64) := by
  norm_num [polynomial155, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry155 : CachedQuarticSign :=
  ⟨polynomial155, 0, (11/64),
    false, .leaf⟩

theorem entry155_checked : entry155.Check := by
  change polynomial155.BernsteinNonnegCheck 0 (11/64)
  exact sign155

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk12
