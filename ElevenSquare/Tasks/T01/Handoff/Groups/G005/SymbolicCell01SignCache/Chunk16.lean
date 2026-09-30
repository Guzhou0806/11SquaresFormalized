import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk16
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial192 : Quartic := ⟨184082017316891286622600541915404061049696757, -244358791874329568185432000000000000000000000, -332906216010427955702751458084595938950303243, 0, 0⟩

theorem sign192 : polynomial192.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial192, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry192 : CachedQuarticSign :=
  ⟨polynomial192, 0, (1/64),
    false, .leaf⟩

theorem entry192_checked : entry192.Check := by
  change polynomial192.BernsteinNonnegCheck 0 (1/64)
  exact sign192

def polynomial193 : Quartic := ⟨1904122774801691038501184800210885027, -2716976406757083536152481007195623440, 4052693964291160000000000000000000000, 45578833242916463847518992804376560, -3285401730510531038501184800210885027⟩

theorem sign193 : polynomial193.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial193, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry193 : CachedQuarticSign :=
  ⟨polynomial193, 0, 1,
    false, .leaf⟩

theorem entry193_checked : entry193.Check := by
  change polynomial193.BernsteinNonnegCheck 0 1
  exact sign193

def polynomial194 : Quartic := ⟨192756378122315563896341226428822239, -159643688211985000000000000000000000, 47756194259106127792682452857644478, -159643688211985000000000000000000000, -145000183863209436103658773571177761⟩

theorem sign194 : polynomial194.BernsteinNonnegCheck (11/16) (23/32) := by
  norm_num [polynomial194, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry194 : CachedQuarticSign :=
  ⟨polynomial194, (11/16), (23/32),
    false, .leaf⟩

theorem entry194_checked : entry194.Check := by
  change polynomial194.BernsteinNonnegCheck (11/16) (23/32)
  exact sign194

def polynomial195 : Quartic := ⟨192756378122315563896341226428822239, 2924458361745064022341459622861155824, -2892055573377285000000000000000000000, -2160359253599365977658540377138844176, 145000183863209436103658773571177761⟩

theorem sign195 : polynomial195.BernsteinNonnegCheck (11/16) (23/32) := by
  norm_num [polynomial195, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry195 : CachedQuarticSign :=
  ⟨polynomial195, (11/16), (23/32),
    false, .leaf⟩

theorem entry195_checked : entry195.Check := by
  change polynomial195.BernsteinNonnegCheck (11/16) (23/32)
  exact sign195

def polynomial196 : Quartic := ⟨195975257013045115883738177246075753364744085, 482382440755070605107280896101686206033977932, -2589679835991216137506280000000000000000000000, -582158246581742949999919103898313793966022068, 328331545537519371582621822753924246635255915⟩

theorem sign196 : polynomial196.BernsteinNonnegCheck (1/16) (1/4) := by
  norm_num [polynomial196, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry196 : CachedQuarticSign :=
  ⟨polynomial196, (1/16), (1/4),
    false, .leaf⟩

theorem entry196_checked : entry196.Check := by
  change polynomial196.BernsteinNonnegCheck (1/16) (1/4)
  exact sign196

def polynomial197 : Quartic := ⟨19736151138642109019031075379416439640059482353, 572664799401543189297207222413633954446516000000, 1736593560576250446964024800000000000000000000000, 538023203161928155269367062413633954446516000000, -844185161722723138219031075379416439640059482353⟩

theorem sign197 : polynomial197.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial197, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry197 : CachedQuarticSign :=
  ⟨polynomial197, 0, 1,
    false, .leaf⟩

theorem entry197_checked : entry197.Check := by
  change polynomial197.BernsteinNonnegCheck 0 1
  exact sign197

def polynomial198 : Quartic := ⟨1978821, 127595441, 999999000, -1872404559, 998020179⟩

theorem sign198 : polynomial198.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial198, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry198 : CachedQuarticSign :=
  ⟨polynomial198, 0, 1,
    false, .leaf⟩

theorem entry198_checked : entry198.Check := by
  change polynomial198.BernsteinNonnegCheck 0 1
  exact sign198

def polynomial199 : Quartic := ⟨20002089177913368083031079796757000000, 43945690316899210224430127707779552941, 106038376251509300000000000000000000000, -819353217486999509775569872292220447059, 737257791151457451916968920203243000000⟩

theorem sign199 : polynomial199.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial199, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry199 : CachedQuarticSign :=
  ⟨polynomial199, 0, (1/64),
    false, .leaf⟩

theorem entry199_checked : entry199.Check := by
  change polynomial199.BernsteinNonnegCheck 0 (1/64)
  exact sign199

def polynomial200 : Quartic := ⟨2001628489252821043243573264176247600551, 1742983620214451661111110000000000000000, -7118609269344955885645316735823752399449, 0, 0⟩

theorem sign200 : polynomial200.BernsteinNonnegCheck (21/64) (19/32) := by
  norm_num [polynomial200, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry200 : CachedQuarticSign :=
  ⟨polynomial200, (21/64), (19/32),
    false, .leaf⟩

theorem entry200_checked : entry200.Check := by
  change polynomial200.BernsteinNonnegCheck (21/64) (19/32)
  exact sign200

def polynomial201 : Quartic := ⟨200416790109357808091167045735720758321510701, 3829211415514244269109951297029011666274578700, 1139011638010532643270560000000000000000000000, -3120569591751173980426128702970988333725421300, -406724456986795500897807045735720758321510701⟩

theorem sign201 : polynomial201.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial201, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry201 : CachedQuarticSign :=
  ⟨polynomial201, 0, 1,
    false, .leaf⟩

theorem entry201_checked : entry201.Check := by
  change polynomial201.BernsteinNonnegCheck 0 1
  exact sign201

def polynomial202 : Quartic := ⟨20069894031722503214113498760850618894434138537819, 23219683056428865188046472479200000000000000000000, -25603447486551457287098140052749381105565861462181, 0, 0⟩

theorem sign202 : polynomial202.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial202, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry202 : CachedQuarticSign :=
  ⟨polynomial202, 0, 1,
    false, .leaf⟩

theorem entry202_checked : entry202.Check := by
  change polynomial202.BernsteinNonnegCheck 0 1
  exact sign202

def polynomial203 : Quartic := ⟨202557640688695377485386113676467897, 1804269807535904668916656267188263900, 1424901860790040000000000000000000000, -3599845992464095331083343732811736100, 3776648340101344622514613886323532103⟩

theorem sign203 : polynomial203.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial203, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry203 : CachedQuarticSign :=
  ⟨polynomial203, 0, 1,
    false, .leaf⟩

theorem entry203_checked : entry203.Check := by
  change polynomial203.BernsteinNonnegCheck 0 1
  exact sign203

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk16
