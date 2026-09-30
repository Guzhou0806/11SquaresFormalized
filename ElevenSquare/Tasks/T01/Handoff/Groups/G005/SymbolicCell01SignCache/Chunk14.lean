import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk14
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial168 : Quartic := ⟨1347851773536090631328680068833365217987, -5992417441165140093540553648190011824880, 6153284704190879080000000000000000000000, -140669436305663373540553648190011824880, -1347854774798019471328680068833365217987⟩

theorem sign168 : polynomial168.BernsteinNonnegCheck (125/128) 1 := by
  norm_num [polynomial168, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry168 : CachedQuarticSign :=
  ⟨polynomial168, (125/128), 1,
    false, .leaf⟩

theorem entry168_checked : entry168.Check := by
  change polynomial168.BernsteinNonnegCheck (125/128) 1
  exact sign168

def polynomial169 : Quartic := ⟨1402324591, 1974214990, -1402324591, 0, 0⟩

theorem sign169 : polynomial169.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial169, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry169 : CachedQuarticSign :=
  ⟨polynomial169, 0, 1,
    false, .leaf⟩

theorem entry169_checked : entry169.Check := by
  change polynomial169.BernsteinNonnegCheck 0 1
  exact sign169

def polynomial170 : Quartic := ⟨141335518947181033209528043085, 5239034776181296400611346122294, -21667159344247560000000000000000, 9984368270843056400611346122294, 5499273097581418966790471956915⟩

theorem sign170 : polynomial170.BernsteinNonnegCheck (19/64) (5/16) := by
  norm_num [polynomial170, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry170 : CachedQuarticSign :=
  ⟨polynomial170, (19/64), (5/16),
    false, .leaf⟩

theorem entry170_checked : entry170.Check := by
  change polynomial170.BernsteinNonnegCheck (19/64) (5/16)
  exact sign170

def polynomial171 : Quartic := ⟨143387081, -447324591, -143387081, 0, 0⟩

theorem sign171 : polynomial171.BernsteinNonnegCheck 0 (1/4) := by
  norm_num [polynomial171, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry171 : CachedQuarticSign :=
  ⟨polynomial171, 0, (1/4),
    false, .leaf⟩

theorem entry171_checked : entry171.Check := by
  change polynomial171.BernsteinNonnegCheck 0 (1/4)
  exact sign171

def polynomial172 : Quartic := ⟨14407845615688102167914330917665884914608135, -110608335636300191133450153902094529045689886, -2075805626415611159665540000000000000000000000, -5544274300675041006322250153902094529045689886, 1276944599744642007059585669082334115085391865⟩

theorem sign172 : polynomial172.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial172, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry172 : CachedQuarticSign :=
  ⟨polynomial172, 0, (1/64),
    false, .leaf⟩

theorem entry172_checked : entry172.Check := by
  change polynomial172.BernsteinNonnegCheck 0 (1/64)
  exact sign172

def polynomial173 : Quartic := ⟨1457396563675246597616178279580604435600, -759814913725026028699037403419339161431, -10065001944458426994848000000000000000000, 1311152691205896222468962596580660838569, 2660196121122913402383821720419395564400⟩

theorem sign173 : polynomial173.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial173, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry173 : CachedQuarticSign :=
  ⟨polynomial173, (21/64), (91/256),
    false, .leaf⟩

theorem entry173_checked : entry173.Check := by
  change polynomial173.BernsteinNonnegCheck (21/64) (91/256)
  exact sign173

def polynomial174 : Quartic := ⟨145999677257581257417792824163, 27833283656869964917978487230210, -104413228906666680000000000000000, 48206596643536604917978487230210, 27867305629409098742582207175837⟩

theorem sign174 : polynomial174.BernsteinNonnegCheck (5/256) (1/4) := by
  norm_num [polynomial174, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry174 : CachedQuarticSign :=
  ⟨polynomial174, (5/256), (1/4),
    false, .leaf⟩

theorem entry174_checked : entry174.Check := by
  change polynomial174.BernsteinNonnegCheck (5/256) (1/4)
  exact sign174

def polynomial175 : Quartic := ⟨14800720, 1178505993, -14800720, 0, 0⟩

theorem sign175 : polynomial175.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial175, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry175 : CachedQuarticSign :=
  ⟨polynomial175, 0, 1,
    false, .leaf⟩

theorem entry175_checked : entry175.Check := by
  change polynomial175.BernsteinNonnegCheck 0 1
  exact sign175

def polynomial176 : Quartic := ⟨14880557062680789777101754339835639316294781759202471, 4984069578058317797095398668275000000000000000000000, 13768850818757983949400101205170639316294781759202471, 0, 0⟩

theorem sign176 : polynomial176.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial176, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry176 : CachedQuarticSign :=
  ⟨polynomial176, 0, 1,
    false, .leaf⟩

theorem entry176_checked : entry176.Check := by
  change polynomial176.BernsteinNonnegCheck 0 1
  exact sign176

def polynomial177 : Quartic := ⟨1488381844655716702035021776501004787115321557, -6850931486854763508362314304520539626009311100, 8398808783785440126794000000000000000000000000, -626885017230999511561274304520539626009311100, -1983147851041724862035021776501004787115321557⟩

theorem sign177 : polynomial177.BernsteinNonnegCheck (27/32) 1 := by
  norm_num [polynomial177, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry177 : CachedQuarticSign :=
  ⟨polynomial177, (27/32), 1,
    false, .leaf⟩

theorem entry177_checked : entry177.Check := by
  change polynomial177.BernsteinNonnegCheck (27/32) 1
  exact sign177

def polynomial178 : Quartic := ⟨1533000893326295029967673791811536999, 263288225622905839789811136165518926002, -1289437903155093120000000000000000000000, 613746525895683679789811136165518926002, 311460200067445464970032326208188463001⟩

theorem sign178 : polynomial178.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial178, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry178 : CachedQuarticSign :=
  ⟨polynomial178, 0, (1/64),
    false, .leaf⟩

theorem entry178_checked : entry178.Check := by
  change polynomial178.BernsteinNonnegCheck 0 (1/64)
  exact sign178

def polynomial179 : Quartic := ⟨155701156845092956067893064929847837986932450662741847, 393731283674497819252656754300360000000000000000000000, -618772092509392076570944390832032162013067549337258153, 0, 0⟩

theorem sign179 : polynomial179.BernsteinNonnegCheck (101/256) (19/32) := by
  norm_num [polynomial179, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry179 : CachedQuarticSign :=
  ⟨polynomial179, (101/256), (19/32),
    false, .leaf⟩

theorem entry179_checked : entry179.Check := by
  change polynomial179.BernsteinNonnegCheck (101/256) (19/32)
  exact sign179

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk14
