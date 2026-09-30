import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def zeroEntry : CachedQuarticSign := ⟨⟨0,0,0,0,0⟩, 0, 1, false, .leaf⟩
def oneEntry : CachedQuarticSign := ⟨⟨1,0,0,0,0⟩, 0, 1, true, .leaf⟩

theorem zeroEntry_checked : zeroEntry.Check := by
  norm_num [zeroEntry, CachedQuarticSign.Check, QuarticIntervalCertificate.Check,
    Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem oneEntry_checked : oneEntry.Check := by
  norm_num [oneEntry, CachedQuarticSign.Check, QuarticIntervalCertificate.Check,
    Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants
