import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk22
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial264 : Quartic := ⟨41410807228890049677039664165412821615, 4069042108590581969222355638374032786, 212076752503018600000000000000000000000, -1722528773499206858030777644361625967214, 1473108953429851590322960335834587178385⟩

theorem sign264 : polynomial264.BernsteinNonnegCheck (5/256) (11/64) := by
  norm_num [polynomial264, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry264 : CachedQuarticSign :=
  ⟨polynomial264, (5/256), (11/64),
    false, .leaf⟩

theorem entry264_checked : entry264.Check := by
  change polynomial264.BernsteinNonnegCheck (5/256) (11/64)
  exact sign264

def polynomial265 : Quartic := ⟨415409169391987443867422280983977490859, 7125561512001340462124168907696286000000, -14105972565773328240000000000000000000000, -657044033625331297875831092303714000000, 6880783534408012556132577719016022509141⟩

theorem sign265 : polynomial265.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial265, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry265 : CachedQuarticSign :=
  ⟨polynomial265, (19/64), (5/16),
    false, .leaf⟩

theorem entry265_checked : entry265.Check := by
  change polynomial265.BernsteinNonnegCheck (19/64) (5/16)
  exact sign265

def polynomial266 : Quartic := ⟨4161854717255640176311416634156058611239176503, 135096275300540274108440627404160458298444114695, 379840638606819318508204520000000000000000000000, 91360173986811994280144707404160458298444114695, -197248931397820413735342336634156058611239176503⟩

theorem sign266 : polynomial266.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial266, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry266 : CachedQuarticSign :=
  ⟨polynomial266, 0, 1,
    false, .leaf⟩

theorem entry266_checked : entry266.Check := by
  change polynomial266.BernsteinNonnegCheck 0 1
  exact sign266

def polynomial267 : Quartic := ⟨4162270513296228706078172088967111795, -166266612095090290113535814135984166568, -4954339825828553160000000000000000000000, 4542772197234724669886464185864015833432, 77604734986283171293921827911032888205⟩

theorem sign267 : polynomial267.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial267, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry267 : CachedQuarticSign :=
  ⟨polynomial267, 0, (1/64),
    false, .leaf⟩

theorem entry267_checked : entry267.Check := by
  change polynomial267.BernsteinNonnegCheck 0 (1/64)
  exact sign267

def polynomial268 : Quartic := ⟨419934206070507770186548136196938021693929652, -611346063065204992584331117768814380039221351, -344061349603329215190660000000000000000000000, 727271454596040484145108882231185619960778649, 287002440119564107429431863803061978306070348⟩

theorem sign268 : polynomial268.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial268, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry268 : CachedQuarticSign :=
  ⟨polynomial268, (101/256), (19/32),
    false, .leaf⟩

theorem entry268_checked : entry268.Check := by
  change polynomial268.BernsteinNonnegCheck (101/256) (19/32)
  exact sign268

def polynomial269 : Quartic := ⟨42358674053104001251595360045522380741444791, 58103213530021543501920000000000000000000000, -296503412368650541046684639954477619258555209, 0, 0⟩

theorem sign269 : polynomial269.BernsteinNonnegCheck (7/32) (5/16) := by
  norm_num [polynomial269, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry269 : CachedQuarticSign :=
  ⟨polynomial269, (7/32), (5/16),
    false, .leaf⟩

theorem entry269_checked : entry269.Check := by
  change polynomial269.BernsteinNonnegCheck (7/32) (5/16)
  exact sign269

def polynomial270 : Quartic := ⟨432091850345336675650834749508400212, 1558394747071580831087291312622899947, -33346111427643760000000000000000000000, -238082719966299168912708687377100053, 5713339958766463324349165250491599788⟩

theorem sign270 : polynomial270.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial270, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry270 : CachedQuarticSign :=
  ⟨polynomial270, 0, (1/64),
    false, .leaf⟩

theorem entry270_checked : entry270.Check := by
  change polynomial270.BernsteinNonnegCheck 0 (1/64)
  exact sign270

def polynomial271 : Quartic := ⟨444185229554039385233285856531383295, -1060584865245478425095129777421918451, 35704496356042095525059207187224828, 3119381207644558425095129777421918451, -569577712916020614766714143468616705⟩

theorem sign271 : polynomial271.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial271, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry271 : CachedQuarticSign :=
  ⟨polynomial271, (101/256), (19/32),
    false, .leaf⟩

theorem entry271_checked : entry271.Check := by
  change polynomial271.BernsteinNonnegCheck (101/256) (19/32)
  exact sign271

def polynomial272 : Quartic := ⟨445666667, 1910000000, -445666667, 0, 0⟩

theorem sign272 : polynomial272.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial272, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry272 : CachedQuarticSign :=
  ⟨polynomial272, 0, 1,
    false, .leaf⟩

theorem entry272_checked : entry272.Check := by
  change polynomial272.BernsteinNonnegCheck 0 1
  exact sign272

def polynomial273 : Quartic := ⟨447324591, 573548324, -447324591, 0, 0⟩

theorem sign273 : polynomial273.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial273, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry273 : CachedQuarticSign :=
  ⟨polynomial273, 0, 1,
    false, .leaf⟩

theorem entry273_checked : entry273.Check := by
  change polynomial273.BernsteinNonnegCheck 0 1
  exact sign273

def polynomial274 : Quartic := ⟨447324591, 573548324, -447324591, 0, 0⟩

theorem sign274 : polynomial274.BernsteinPosCheck 0 1 := by
  norm_num [polynomial274, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry274 : CachedQuarticSign :=
  ⟨polynomial274, 0, 1,
    true, .leaf⟩

theorem entry274_checked : entry274.Check := by
  change polynomial274.BernsteinPosCheck 0 1
  exact sign274

def polynomial275 : Quartic := ⟨451066457081486167229164066797065975, 1148469319706324622514613886323532103, -1351030939604980000000000000000000000, 2425621379706324622514613886323532103, 899960503313533832770835933202934025⟩

theorem sign275 : polynomial275.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial275, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry275 : CachedQuarticSign :=
  ⟨polynomial275, 0, 1,
    false, .leaf⟩

theorem entry275_checked : entry275.Check := by
  change polynomial275.BernsteinNonnegCheck 0 1
  exact sign275

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk22
