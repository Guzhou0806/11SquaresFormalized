import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk10
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial120 : Quartic := ⟨0, -203644803, 19699817840, 203644803, 0⟩

theorem sign120 : polynomial120.BernsteinNonnegCheck (11/16) (27/32) := by
  norm_num [polynomial120, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry120 : CachedQuarticSign :=
  ⟨polynomial120, (11/16), (27/32),
    false, .leaf⟩

theorem entry120_checked : entry120.Check := by
  change polynomial120.BernsteinNonnegCheck (11/16) (27/32)
  exact sign120

def polynomial121 : Quartic := ⟨0, -356489068, 10104575587, 356489068, 0⟩

theorem sign121 : polynomial121.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial121, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry121 : CachedQuarticSign :=
  ⟨polynomial121, (1/2), (19/32),
    false, .leaf⟩

theorem entry121_checked : entry121.Check := by
  change polynomial121.BernsteinNonnegCheck (1/2) (19/32)
  exact sign121

def polynomial122 : Quartic := ⟨0, 1, 0, 0, 0⟩

theorem sign122 : polynomial122.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial122, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry122 : CachedQuarticSign :=
  ⟨polynomial122, 0, 1,
    false, .leaf⟩

theorem entry122_checked : entry122.Check := by
  change polynomial122.BernsteinNonnegCheck 0 1
  exact sign122

def polynomial123 : Quartic := ⟨0, 1, 0, 0, 0⟩

theorem sign123 : polynomial123.BernsteinPosCheck (5/64) 1 := by
  norm_num [polynomial123, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry123 : CachedQuarticSign :=
  ⟨polynomial123, (5/64), 1,
    true, .leaf⟩

theorem entry123_checked : entry123.Check := by
  change polynomial123.BernsteinPosCheck (5/64) 1
  exact sign123

def polynomial124 : Quartic := ⟨0, 1, 18, -1, 0⟩

theorem sign124 : polynomial124.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial124, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry124 : CachedQuarticSign :=
  ⟨polynomial124, 0, 1,
    false, .leaf⟩

theorem entry124_checked : entry124.Check := by
  change polynomial124.BernsteinNonnegCheck 0 1
  exact sign124

def polynomial125 : Quartic := ⟨0, 1872970031715282124606689500000, -3653246630888066491807396472577, 1947022328284717875393310500000, 0⟩

theorem sign125 : polynomial125.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial125, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry125 : CachedQuarticSign :=
  ⟨polynomial125, 0, 1,
    false, .leaf⟩

theorem entry125_checked : entry125.Check := by
  change polynomial125.BernsteinNonnegCheck 0 1
  exact sign125

def polynomial126 : Quartic := ⟨0, 2048209971556532712480642864708, -3917628419250284490908411533097, 1771782388443467287519357135292, 0⟩

theorem sign126 : polynomial126.BernsteinNonnegCheck (1/2) (19/32) := by
  norm_num [polynomial126, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry126 : CachedQuarticSign :=
  ⟨polynomial126, (1/2), (19/32),
    false, .leaf⟩

theorem entry126_checked : entry126.Check := by
  change polynomial126.BernsteinNonnegCheck (1/2) (19/32)
  exact sign126

def polynomial127 : Quartic := ⟨0, 344203052777008872439587024011, -761483059593725908721748785576, 419795419222991127560412975989, 0⟩

theorem sign127 : polynomial127.BernsteinNonnegCheck (125/128) 1 := by
  norm_num [polynomial127, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry127 : CachedQuarticSign :=
  ⟨polynomial127, (125/128), 1,
    false, .leaf⟩

theorem entry127_checked : entry127.Check := by
  change polynomial127.BernsteinNonnegCheck (125/128) 1
  exact sign127

def polynomial128 : Quartic := ⟨0, 3612283640997718582269, -6978750462041065519158, 4387700359002281417731, 0⟩

theorem sign128 : polynomial128.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial128, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry128 : CachedQuarticSign :=
  ⟨polynomial128, 0, 1,
    false, .leaf⟩

theorem entry128_checked : entry128.Check := by
  change polynomial128.BernsteinNonnegCheck 0 1
  exact sign128

def polynomial129 : Quartic := ⟨0, 3898947152390472875864390201993, -7637784047390268073717646121040, 3741037567609527124135609798007, 0⟩

theorem sign129 : polynomial129.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial129, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry129 : CachedQuarticSign :=
  ⟨polynomial129, 0, 1,
    false, .leaf⟩

theorem entry129_checked : entry129.Check := by
  change polynomial129.BernsteinNonnegCheck 0 1
  exact sign129

def polynomial130 : Quartic := ⟨0, 95500000, 9422666667, -95500000, 0⟩

theorem sign130 : polynomial130.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial130, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry130 : CachedQuarticSign :=
  ⟨polynomial130, 0, 1,
    false, .leaf⟩

theorem entry130_checked : entry130.Check := by
  change polynomial130.BernsteinNonnegCheck 0 1
  exact sign130

def polynomial131 : Quartic := ⟨1, 0, -1, 0, 0⟩

theorem sign131 : polynomial131.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial131, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry131 : CachedQuarticSign :=
  ⟨polynomial131, 0, 1,
    false, .leaf⟩

theorem entry131_checked : entry131.Check := by
  change polynomial131.BernsteinNonnegCheck 0 1
  exact sign131

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk10
