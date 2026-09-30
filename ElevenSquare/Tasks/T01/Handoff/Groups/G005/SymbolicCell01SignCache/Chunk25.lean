import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk25
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial300 : Quartic := ⟨53047327564656742560072290273357876405614500, 838890175599821441132634226497729824482478621, 284193534236860539868420000000000000000000000, -629567621134077018135825773502270175517521379, 1097784039699316634817447709726642123594385500⟩

theorem sign300 : polynomial300.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial300, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry300 : CachedQuarticSign :=
  ⟨polynomial300, 0, 1,
    false, .leaf⟩

theorem entry300_checked : entry300.Check := by
  change polynomial300.BernsteinNonnegCheck 0 1
  exact sign300

def polynomial301 : Quartic := ⟨53278284164208618358801423869865093497672225, -179753230442779782834761776501004787115321557, -2470776700735866151698500000000000000000000000, -3291776465254661781235281776501004787115321557, 1922732410185649373339698576130134906502327775⟩

theorem sign301 : polynomial301.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial301, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry301 : CachedQuarticSign :=
  ⟨polynomial301, 0, (1/64),
    false, .leaf⟩

theorem entry301_checked : entry301.Check := by
  change polynomial301.BernsteinNonnegCheck 0 (1/64)
  exact sign301

def polynomial302 : Quartic := ⟨540223, -1419504, -540223, 0, 0⟩

theorem sign302 : polynomial302.BernsteinNonnegCheck 0 (7/128) := by
  norm_num [polynomial302, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry302 : CachedQuarticSign :=
  ⟨polynomial302, 0, (7/128),
    false, .leaf⟩

theorem entry302_checked : entry302.Check := by
  change polynomial302.BernsteinNonnegCheck 0 (7/128)
  exact sign302

def polynomial303 : Quartic := ⟨540892505, 2422649182, -540892505, 0, 0⟩

theorem sign303 : polynomial303.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial303, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry303 : CachedQuarticSign :=
  ⟨polynomial303, 0, 1,
    false, .leaf⟩

theorem entry303_checked : entry303.Check := by
  change polynomial303.BernsteinNonnegCheck 0 1
  exact sign303

def polynomial304 : Quartic := ⟨54750379930560550523209908430444164203340220, 737403682129756254813371243666906431163328733, 284193534236860539868420000000000000000000000, -731054114604142204455088756333093568836671267, 1096080987333412826854310091569555835796659780⟩

theorem sign304 : polynomial304.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial304, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry304 : CachedQuarticSign :=
  ⟨polynomial304, 0, 1,
    false, .leaf⟩

theorem entry304_checked : entry304.Check := by
  change polynomial304.BernsteinNonnegCheck 0 1
  exact sign304

def polynomial305 : Quartic := ⟨5685988253112007300675333243222437216104977189, -169188618920475931218691577747188510707030000000, 580731588402848423402679802000000000000000000000, -302554653648281523483665413747188510707030000000, -167286544939770390563355135243222437216104977189⟩

theorem sign305 : polynomial305.BernsteinNonnegCheck (21/64) (19/32) := by
  norm_num [polynomial305, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry305 : CachedQuarticSign :=
  ⟨polynomial305, (21/64), (19/32),
    false, .leaf⟩

theorem entry305_checked : entry305.Check := by
  change polynomial305.BernsteinNonnegCheck (21/64) (19/32)
  exact sign305

def polynomial306 : Quartic := ⟨571084472878405712084224316013742540743, -4722926882451339536259398851542610000000, 11020786890912286739696400000000000000000, -4904296496271313536405158851542610000000, -2958897430973090051780624316013742540743⟩

theorem sign306 : polynomial306.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial306, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry306 : CachedQuarticSign :=
  ⟨polynomial306, (1/2), (19/32),
    false, .leaf⟩

theorem entry306_checked : entry306.Check := by
  change polynomial306.BernsteinNonnegCheck (1/2) (19/32)
  exact sign306

def polynomial307 : Quartic := ⟨57174139565378857459787690923275308843015035, 508036179331516066444866135354128843674489874, 80568868094317715247640000000000000000000000, -341462593098143312350653864645871156325510126, 174417560074448394234412309076724691156984965⟩

theorem sign307 : polynomial307.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial307, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry307 : CachedQuarticSign :=
  ⟨polynomial307, 0, 1,
    false, .leaf⟩

theorem entry307_checked : entry307.Check := by
  change polynomial307.BernsteinNonnegCheck 0 1
  exact sign307

def polynomial308 : Quartic := ⟨580075954653000000, -167607833328253795, 1164686158719998178, 167607833328253795, 580075954653000000⟩

theorem sign308 : polynomial308.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial308, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry308 : CachedQuarticSign :=
  ⟨polynomial308, 0, 1,
    false, .leaf⟩

theorem entry308_checked : entry308.Check := by
  change polynomial308.BernsteinNonnegCheck 0 1
  exact sign308

def polynomial309 : Quartic := ⟨58482653901339204552107091177, -92289331635578197697982015130, -791116787330264926409876182354, 2002287421635578197697982015130, -896516391098660795447892908823⟩

theorem sign309 : polynomial309.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial309, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry309 : CachedQuarticSign :=
  ⟨polynomial309, (1/2), (19/32),
    false, .leaf⟩

theorem entry309_checked : entry309.Check := by
  change polynomial309.BernsteinNonnegCheck (1/2) (19/32)
  exact sign309

def polynomial310 : Quartic := ⟨58569620045466131536253624197909500000, -105344113058706653704917062840797924399, 177025310046086293000000000000000000000, -33188277221614646704917062840797924399, -58569682340830471536253624197909500000⟩

theorem sign310 : polynomial310.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial310, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry310 : CachedQuarticSign :=
  ⟨polynomial310, 0, 1,
    false, .leaf⟩

theorem entry310_checked : entry310.Check := by
  change polynomial310.BernsteinNonnegCheck 0 1
  exact sign310

def polynomial311 : Quartic := ⟨58690675764106230334475000000, 277934288865207917850582993845, -3901373201568869444264647446042, 7362058071134792082149417006155, -3761305504235893769665525000000⟩

theorem sign311 : polynomial311.BernsteinNonnegCheck (5/256) (11/64) := by
  norm_num [polynomial311, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry311 : CachedQuarticSign :=
  ⟨polynomial311, (5/256), (11/64),
    false, .leaf⟩

theorem entry311_checked : entry311.Check := by
  change polynomial311.BernsteinNonnegCheck (5/256) (11/64)
  exact sign311

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk25
