import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk03
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial036 : Quartic := ⟨-178351627923530959898414802646928106214753223874258467, 325440242749146226609161747722600000000000000000000000, 11711935429575279761811284094311893785246776125741533, 0, 0⟩

theorem sign036 : polynomial036.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial036, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry036 : CachedQuarticSign :=
  ⟨polynomial036, (11/16), (27/32),
    false, .leaf⟩

theorem entry036_checked : entry036.Check := by
  change polynomial036.BernsteinNonnegCheck (11/16) (27/32)
  exact sign036

def polynomial037 : Quartic := ⟨-178842210407904148770924463940, 550750524354497480440339232467, 4177676780815808297541848927880, -550750524354497480440339232467, -3998834570407904148770924463940⟩

theorem sign037 : polynomial037.BernsteinNonnegCheck (61/128) (19/32) := by
  norm_num [polynomial037, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry037 : CachedQuarticSign :=
  ⟨polynomial037, (61/128), (19/32),
    false, .leaf⟩

theorem entry037_checked : entry037.Check := by
  change polynomial037.BernsteinNonnegCheck (61/128) (19/32)
  exact sign037

def polynomial038 : Quartic := ⟨-18267473734416595014121875065175116830799977, 38331286314288184804807000000000000000000000, -17245316934671468972834875065175116830799977, 0, 0⟩

theorem sign038 : polynomial038.BernsteinNonnegCheck (125/128) 1 := by
  norm_num [polynomial038, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry038 : CachedQuarticSign :=
  ⟨polynomial038, (125/128), 1,
    false, .leaf⟩

theorem entry038_checked : entry038.Check := by
  change polynomial038.BernsteinNonnegCheck (125/128) 1
  exact sign038

def polynomial039 : Quartic := ⟨-186438354766224298786370331702, -101297995274498416788219493869, 1244930669158484000000000000000, -783207137343714416788219493869, 527392473811764298786370331702⟩

theorem sign039 : polynomial039.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial039, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry039 : CachedQuarticSign :=
  ⟨polynomial039, (1/2), (19/32),
    false, .leaf⟩

theorem entry039_checked : entry039.Check := by
  change polynomial039.BernsteinNonnegCheck (1/2) (19/32)
  exact sign039

def polynomial040 : Quartic := ⟨-1903695183325941165510981500000, 3741041387609527124135609798007, 10397500738385742695683121040, 3898950972390472875864390201993, -5723691363325941165510981500000⟩

theorem sign040 : polynomial040.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial040, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry040 : CachedQuarticSign :=
  ⟨polynomial040, (11/16), (27/32),
    false, .leaf⟩

theorem entry040_checked : entry040.Check := by
  change polynomial040.BernsteinNonnegCheck (11/16) (27/32)
  exact sign040

def polynomial041 : Quartic := ⟨-195822259142526691916968920203243000000, 369556548393880610224430127707779552941, 537687072892389420000000000000000000000, -1144964075563980909775569872292220447059, 521433442831017391916968920203243000000⟩

theorem sign041 : polynomial041.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial041, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry041 : CachedQuarticSign :=
  ⟨polynomial041, (11/16), (27/32),
    false, .leaf⟩

theorem entry041_checked : entry041.Check := by
  change polynomial041.BernsteinNonnegCheck (11/16) (27/32)
  exact sign041

def polynomial042 : Quartic := ⟨-19836701283538308045995344407576407829, 172659478656352048000000000000000000000, -169917745797869176091990688815152815658, 172659478656352048000000000000000000000, -150081044514330868045995344407576407829⟩

theorem sign042 : polynomial042.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial042, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry042 : CachedQuarticSign :=
  ⟨polynomial042, (11/16), (27/32),
    false, .leaf⟩

theorem entry042_checked : entry042.Check := by
  change polynomial042.BernsteinNonnegCheck (11/16) (27/32)
  exact sign042

def polynomial043 : Quartic := ⟨-19838760065410631377119972913306926206090679715, 113759496562038800484446055078156235949342964706, 713567813449871737174172240000000000000000000000, -989324497413024972107418904921843764050657035294, 185683223996360396495107572913306926206090679715⟩

theorem sign043 : polynomial043.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial043, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry043 : CachedQuarticSign :=
  ⟨polynomial043, (1/2), (19/32),
    false, .leaf⟩

theorem entry043_checked : entry043.Check := by
  change polynomial043.BernsteinNonnegCheck (1/2) (19/32)
  exact sign043

def polynomial044 : Quartic := ⟨-218962233217180253958325965991147425645796239, 884814292197576180322840000000000000000000000, -468350570986260360174445965991147425645796239, 0, 0⟩

theorem sign044 : polynomial044.BernsteinNonnegCheck (19/64) (91/256) := by
  norm_num [polynomial044, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry044 : CachedQuarticSign :=
  ⟨polynomial044, (19/64), (91/256),
    false, .leaf⟩

theorem entry044_checked : entry044.Check := by
  change polynomial044.BernsteinNonnegCheck (19/64) (91/256)
  exact sign044

def polynomial045 : Quartic := ⟨-2204780522000520811920377111360193423943558359163, 3318894175012735584810601838187054643937984000000, 12674481777466119056135966240000000000000000000000, -6163183829201805144714305201812945356062016000000, -551569650620708522879622888639806576056441640837⟩

theorem sign045 : polynomial045.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial045, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry045 : CachedQuarticSign :=
  ⟨polynomial045, (11/16), (27/32),
    false, .leaf⟩

theorem entry045_checked : entry045.Check := by
  change polynomial045.BernsteinNonnegCheck (11/16) (27/32)
  exact sign045

def polynomial046 : Quartic := ⟨-2269544784932732783711226210631, 4074148674057207066773025976424, 5630231129763240000000000000000, -11784706027072232933226974023576, 5679085975388132783711226210631⟩

theorem sign046 : polynomial046.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial046, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry046 : CachedQuarticSign :=
  ⟨polynomial046, (1/2), (19/32),
    false, .leaf⟩

theorem entry046_checked : entry046.Check := by
  change polynomial046.BernsteinNonnegCheck (1/2) (19/32)
  exact sign046

def polynomial047 : Quartic := ⟨-233490540891655248409669902500331489268379249, 401901285763727174935894132595715730104837390, 236432680455843143200425000000000000000000000, -350239350679578109890625867404284269895162610, -175642288413026970135605097499668510731620751⟩

theorem sign047 : polynomial047.BernsteinNonnegCheck (11/16) (23/32) := by
  norm_num [polynomial047, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry047 : CachedQuarticSign :=
  ⟨polynomial047, (11/16), (23/32),
    false, .leaf⟩

theorem entry047_checked : entry047.Check := by
  change polynomial047.BernsteinNonnegCheck (11/16) (23/32)
  exact sign047

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk03
