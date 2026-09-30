import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk15
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial180 : Quartic := ⟨16524247066214531983373244234007808299, 3745501981507136728946065065190296109411, -14484496021629493860000000000000000000000, 6917757422688523288946065065190296109411, 3754222613083154568016626755765992191701⟩

theorem sign180 : polynomial180.BernsteinNonnegCheck (5/256) (1/4) := by
  norm_num [polynomial180, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry180 : CachedQuarticSign :=
  ⟨polynomial180, (5/256), (1/4),
    false, .leaf⟩

theorem entry180_checked : entry180.Check := by
  change polynomial180.BernsteinNonnegCheck (5/256) (1/4)
  exact sign180

def polynomial181 : Quartic := ⟨16614958118883675189376858924243661150917023, 51149903163182312922803563901327163766782980, -241022857502363357115089600000000000000000000, -60625863440918347715250836098672836233217020, 27928542318119368446439141075756338849082977⟩

theorem sign181 : polynomial181.BernsteinNonnegCheck (5/64) (1/4) := by
  norm_num [polynomial181, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry181 : CachedQuarticSign :=
  ⟨polynomial181, (5/64), (1/4),
    false, .leaf⟩

theorem entry181_checked : entry181.Check := by
  change polynomial181.BernsteinNonnegCheck (5/64) (1/4)
  exact sign181

def polynomial182 : Quartic := ⟨171305796479919045552640541915404061049696757, 516988233327319242325352000000000000000000000, -320129995173455714632791458084595938950303243, 0, 0⟩

theorem sign182 : polynomial182.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial182, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry182 : CachedQuarticSign :=
  ⟨polynomial182, 0, 1,
    false, .leaf⟩

theorem entry182_checked : entry182.Check := by
  change polynomial182.BernsteinNonnegCheck 0 1
  exact sign182

def polynomial183 : Quartic := ⟨171730355432967702308293581315322905827956179, 1722108554420787597917113435309944040883854884, 474719127961955255779880000000000000000000000, -1427787459232370726512406564690055959116145116, -104168147282888871839053581315322905827956179⟩

theorem sign183 : polynomial183.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial183, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry183 : CachedQuarticSign :=
  ⟨polynomial183, 0, 1,
    false, .leaf⟩

theorem entry183_checked : entry183.Check := by
  change polynomial183.BernsteinNonnegCheck 0 1
  exact sign183

def polynomial184 : Quartic := ⟨17422745676230030183937821681351, -7147484805475789857826251618854, 4335648248503351121412276212238, -14814699830067090142173748381146, -8669501339171569816062178318649⟩

theorem sign184 : polynomial184.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial184, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry184 : CachedQuarticSign :=
  ⟨polynomial184, (91/256), (25/64),
    false, .leaf⟩

theorem entry184_checked : entry184.Check := by
  change polynomial184.BernsteinNonnegCheck (91/256) (25/64)
  exact sign184

def polynomial185 : Quartic := ⟨174831, 1072844, -174831, 0, 0⟩

theorem sign185 : polynomial185.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial185, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry185 : CachedQuarticSign :=
  ⟨polynomial185, 0, 1,
    false, .leaf⟩

theorem entry185_checked : entry185.Check := by
  change polynomial185.BernsteinNonnegCheck 0 1
  exact sign185

def polynomial186 : Quartic := ⟨174831, 1072844, -174831, 0, 0⟩

theorem sign186 : polynomial186.BernsteinPosCheck 0 1 := by
  norm_num [polynomial186, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry186 : CachedQuarticSign :=
  ⟨polynomial186, 0, 1,
    true, .leaf⟩

theorem entry186_checked : entry186.Check := by
  change polynomial186.BernsteinPosCheck 0 1
  exact sign186

def polynomial187 : Quartic := ⟨1756273743578179168912708687377100053, 28929047019913306702603338998033600848, 8425814448337400000000000000000000000, -50054039453597813297396661001966399152, 3076585770683460831087291312622899947⟩

theorem sign187 : polynomial187.BernsteinNonnegCheck (3/4) (7/8) := by
  norm_num [polynomial187, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry187 : CachedQuarticSign :=
  ⟨polynomial187, (3/4), (7/8),
    false, .leaf⟩

theorem entry187_checked : entry187.Check := by
  change polynomial187.BernsteinNonnegCheck (3/4) (7/8)
  exact sign187

def polynomial188 : Quartic := ⟨1756273743578179168912708687377100053, 828667122662440000000000000000000000, -1320312027105281662174582625245799894, 828667122662440000000000000000000000, -3076585770683460831087291312622899947⟩

theorem sign188 : polynomial188.BernsteinNonnegCheck (3/4) (115/128) := by
  norm_num [polynomial188, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry188 : CachedQuarticSign :=
  ⟨polynomial188, (3/4), (115/128),
    false, .leaf⟩

theorem entry188_checked : entry188.Check := by
  change polynomial188.BernsteinNonnegCheck (3/4) (115/128)
  exact sign188

def polynomial189 : Quartic := ⟨178240485131207849803425267825549682660627323, 1692812970817051938905952336866228647811854884, 474719127961955255779880000000000000000000000, -1457083042836106385523567663133771352188145116, -110678276981129019334185267825549682660627323⟩

theorem sign189 : polynomial189.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial189, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry189 : CachedQuarticSign :=
  ⟨polynomial189, 0, 1,
    false, .leaf⟩

theorem entry189_checked : entry189.Check := by
  change polynomial189.BernsteinNonnegCheck 0 1
  exact sign189

def polynomial190 : Quartic := ⟨17959370998719597036745450451371914467, 395186524893056778122927260228675517986, 3289910568260224395700419582588379207038, 3986713906648552501877072739771324482014, -3399593669121529922963254549548628085533⟩

theorem sign190 : polynomial190.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial190, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry190 : CachedQuarticSign :=
  ⟨polynomial190, 0, 1,
    false, .leaf⟩

theorem entry190_checked : entry190.Check := by
  change polynomial190.BernsteinNonnegCheck 0 1
  exact sign190

def polynomial191 : Quartic := ⟨179736409974215429906546778938129, -118671098628070130662675728840000, -58486934748304620885475110763742, -148794766439129869337324271160000, -103201024149784570093453221061871⟩

theorem sign191 : polynomial191.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial191, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry191 : CachedQuarticSign :=
  ⟨polynomial191, (91/256), (25/64),
    false, .leaf⟩

theorem entry191_checked : entry191.Check := by
  change polynomial191.BernsteinNonnegCheck (91/256) (25/64)
  exact sign191

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk15
