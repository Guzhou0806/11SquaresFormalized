import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk15
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_234 : Quartic :=
  ⟨(9999593093062006619361527423 : ℚ), (7152296588781420436149865054846 : ℚ), (-19999186186124013238723054846 : ℚ), (-7152296588781420436149865054846 : ℚ), (9999593093062006619361527423 : ℚ)⟩

theorem sign_234_00 :
    polynomial_234.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_234, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_234_00

def entry_234_00 : CachedQuarticSign :=
  ⟨polynomial_234, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_234_00_checked : entry_234_00.Check := by
  change polynomial_234.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_234_00

def cache : List CachedQuarticSign :=
  [entry_234_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_234_00.Check ∧ True
  exact ⟨entry_234_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk15
