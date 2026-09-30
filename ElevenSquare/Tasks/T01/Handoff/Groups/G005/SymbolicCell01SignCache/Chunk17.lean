import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk17
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial204 : Quartic := ⟨2048209971556532712480642864708, -3917628419250284490908411533097, 3819992360000000000000000000000, -3917628419250284490908411533097, 1771782388443467287519357135292⟩

theorem sign204 : polynomial204.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial204, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry204 : CachedQuarticSign :=
  ⟨polynomial204, (11/16), (27/32),
    false, .leaf⟩

theorem entry204_checked : entry204.Check := by
  change polynomial204.BernsteinNonnegCheck (11/16) (27/32)
  exact sign204

def polynomial205 : Quartic := ⟨205168224362020654893467824257252916568644675, -2041015875364431216878507045735720758321510701, -439483659660711430422620000000000000000000000, 1433874628268277907889532954264279241678489299, 28007768421253082722512175742747083431355325⟩

theorem sign205 : polynomial205.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial205, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry205 : CachedQuarticSign :=
  ⟨polynomial205, 0, (1/64),
    false, .leaf⟩

theorem entry205_checked : entry205.Check := by
  change polynomial205.BernsteinNonnegCheck 0 (1/64)
  exact sign205

def polynomial206 : Quartic := ⟨20945393598331782013941384016022509141, 890464879167814906113357520549802000000, 7084566756073771322613695893674986981718, 9810607046885528613886642479450198000000, -7275240014001668217986058615983977490859⟩

theorem sign206 : polynomial206.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial206, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry206 : CachedQuarticSign :=
  ⟨polynomial206, 0, 1,
    false, .leaf⟩

theorem entry206_checked : entry206.Check := by
  change polynomial206.BernsteinNonnegCheck 0 1
  exact sign206

def polynomial207 : Quartic := ⟨213896784211823068987451655802782654447731423, -1601331250379767520078331311688696530021950465, -701713278498702973866340000000000000000000000, 3583827641393722335893508688311303469978049535, 910508010434316420559728344197217345552268577⟩

theorem sign207 : polynomial207.BernsteinNonnegCheck (7/64) (1/8) := by
  norm_num [polynomial207, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry207 : CachedQuarticSign :=
  ⟨polynomial207, (7/64), (1/8),
    false, .leaf⟩

theorem entry207_checked : entry207.Check := by
  change polynomial207.BernsteinNonnegCheck (7/64) (1/8)
  exact sign207

def polynomial208 : Quartic := ⟨215338668076366188195602693039704258367424039, 15156116418199640559475336347641647386399816, -328375387167252199319924000000000000000000000, -294326712912958615330820663652358352613600184, 104859174127654087833441306960295741632575961⟩

theorem sign208 : polynomial208.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial208, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry208 : CachedQuarticSign :=
  ⟨polynomial208, (91/256), (25/64),
    false, .leaf⟩

theorem entry208_checked : entry208.Check := by
  change polynomial208.BernsteinNonnegCheck (91/256) (25/64)
  exact sign208

def polynomial209 : Quartic := ⟨21750789342683220259441307628098537983454905, 199787482062981183338375575334274989719061724, -4151611252831222319331080000000000000000000000, -10667544448014500447039224424665725010280938276, 2560954101377976998195558692371901462016545095⟩

theorem sign209 : polynomial209.BernsteinNonnegCheck (5/256) (5/64) := by
  norm_num [polynomial209, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry209 : CachedQuarticSign :=
  ⟨polynomial209, (5/256), (5/64),
    false, .leaf⟩

theorem entry209_checked : entry209.Check := by
  change polynomial209.BernsteinNonnegCheck (5/256) (5/64)
  exact sign209

def polynomial210 : Quartic := ⟨22407658304100090895800200551677278877998457, -196244863520214422594514623928527246980190000, 435254478654477571648196000000000000000000000, -38973679972430160155402623928527246980190000, 35293370646714020898563799448322721122001543⟩

theorem sign210 : polynomial210.BernsteinNonnegCheck (11/16) (7/8) := by
  norm_num [polynomial210, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry210 : CachedQuarticSign :=
  ⟨polynomial210, (11/16), (7/8),
    false, .leaf⟩

theorem entry210_checked : entry210.Check := by
  change polynomial210.BernsteinNonnegCheck (11/16) (7/8)
  exact sign210

def polynomial211 : Quartic := ⟨225748904643057321996884472680283719850148523, 817987514377856744964160000000000000000000000, -8531536635294965407018555527319716280149851477, 0, 0⟩

theorem sign211 : polynomial211.BernsteinNonnegCheck (1/8) (11/64) := by
  norm_num [polynomial211, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry211 : CachedQuarticSign :=
  ⟨polynomial211, (1/8), (11/64),
    false, .leaf⟩

theorem entry211_checked : entry211.Check := by
  change polynomial211.BernsteinNonnegCheck (1/8) (11/64)
  exact sign211

def polynomial212 : Quartic := ⟨226148535643458595434396414688865323514565363, 388250881423872908845613780883148976962869274, -2589679835991216137506280000000000000000000000, -676289805912940646261586219116851023037130726, 298158266907105892031963585311134676485434637⟩

theorem sign212 : polynomial212.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial212, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry212 : CachedQuarticSign :=
  ⟨polynomial212, (19/64), (5/16),
    false, .leaf⟩

theorem entry212_checked : entry212.Check := by
  change polynomial212.BernsteinNonnegCheck (19/64) (5/16)
  exact sign212

def polynomial213 : Quartic := ⟨23259196596395344399966289190690229009341680, 346957498120939491689191545771184731697402099, 100858172873280493690652500000000000000000000, -284272315686471544183658454228815268302597901, -31930787766855273296053789190690229009341680⟩

theorem sign213 : polynomial213.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial213, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry213 : CachedQuarticSign :=
  ⟨polynomial213, 0, 1,
    false, .leaf⟩

theorem entry213_checked : entry213.Check := by
  change polynomial213.BernsteinNonnegCheck 0 1
  exact sign213

def polynomial214 : Quartic := ⟨240467538591019787658408125777676944938838887, 654613302557156957044688000000000000000000000, -844609871673269855246359874222323055061161113, 0, 0⟩

theorem sign214 : polynomial214.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial214, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry214 : CachedQuarticSign :=
  ⟨polynomial214, 0, 1,
    false, .leaf⟩

theorem entry214_checked : entry214.Check := by
  change polynomial214.BernsteinNonnegCheck 0 1
  exact sign214

def polynomial215 : Quartic := ⟨24340055165899348565655968875389171031661375, 68215158572738721049177201370423353439135836, 212932417168248234131396000000000000000000000, -309338291130924738804654798629576646560864164, 31321178454564623126628031124610828968338625⟩

theorem sign215 : polynomial215.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial215, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry215 : CachedQuarticSign :=
  ⟨polynomial215, 0, 1,
    false, .leaf⟩

theorem entry215_checked : entry215.Check := by
  change polynomial215.BernsteinNonnegCheck 0 1
  exact sign215

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk17
