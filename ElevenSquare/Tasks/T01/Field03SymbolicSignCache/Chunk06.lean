import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk06
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial_096 : Quartic :=
  ⟨(0 : ℚ), (243775305609289781925067472577 : ℚ), (19999186186124013238723054846 : ℚ), (7396071894390710218074932527423 : ℚ), (0 : ℚ)⟩

theorem sign_096_00 :
    polynomial_096.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_096, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_096_00

def entry_096_00 : CachedQuarticSign :=
  ⟨polynomial_096, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_096_00_checked : entry_096_00.Check := by
  change polynomial_096.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_096_00

def polynomial_097 : Quartic :=
  ⟨(0 : ℚ), (3576148294390710218074932527423 : ℚ), (-19999186186124013238723054846 : ℚ), (-3576148294390710218074932527423 : ℚ), (0 : ℚ)⟩

theorem sign_097_00 :
    polynomial_097.BernsteinNonnegCheck (1387/4096 : ℚ) (1605/4096 : ℚ) := by
  norm_num [polynomial_097, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_097_00

def entry_097_00 : CachedQuarticSign :=
  ⟨polynomial_097, (1387/4096 : ℚ), (1605/4096 : ℚ),
    false, .leaf⟩

theorem entry_097_00_checked : entry_097_00.Check := by
  change polynomial_097.BernsteinNonnegCheck (1387/4096 : ℚ) (1605/4096 : ℚ)
  exact sign_097_00

def polynomial_098 : Quartic :=
  ⟨(0 : ℚ), (3618897047469289781925067472577 : ℚ), (7053527066124013238723054846 : ℚ), (-3618897047469289781925067472577 : ℚ), (0 : ℚ)⟩

theorem sign_098_00 :
    polynomial_098.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_098, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_098_00

def entry_098_00 : CachedQuarticSign :=
  ⟨polynomial_098, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_098_00_checked : entry_098_00.Check := by
  change polynomial_098.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_098_00

def polynomial_099 : Quartic :=
  ⟨(0 : ℚ), (4059078389616380613738770794877 : ℚ), (-1474903820405224422426026780754 : ℚ), (-4059078389616380613738770794877 : ℚ), (0 : ℚ)⟩

theorem sign_099_00 :
    polynomial_099.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ) := by
  norm_num [polynomial_099, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_099_00

def entry_099_00 : CachedQuarticSign :=
  ⟨polynomial_099, (677/4096 : ℚ), (897/2048 : ℚ),
    false, .leaf⟩

theorem entry_099_00_checked : entry_099_00.Check := by
  change polynomial_099.BernsteinNonnegCheck (677/4096 : ℚ) (897/2048 : ℚ)
  exact sign_099_00

def polynomial_100 : Quartic :=
  ⟨(0 : ℚ), (4340682378653005790625575470623 : ℚ), (827620719113840713910418021754 : ℚ), (-4340682378653005790625575470623 : ℚ), (0 : ℚ)⟩

theorem sign_100_00 :
    polynomial_100.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_100, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_100_00

def entry_100_00 : CachedQuarticSign :=
  ⟨polynomial_100, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_100_00_checked : entry_100_00.Check := by
  change polynomial_100.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_100_00

def polynomial_101 : Quartic :=
  ⟨(1 : ℚ), (0 : ℚ), (-1 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_101_00 :
    polynomial_101.BernsteinPosCheck (1/4096 : ℚ) (4069/4096 : ℚ) := by
  norm_num [polynomial_101, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_101_00

def entry_101_00 : CachedQuarticSign :=
  ⟨polynomial_101, (1/4096 : ℚ), (4069/4096 : ℚ),
    true, .leaf⟩

theorem entry_101_00_checked : entry_101_00.Check := by
  change polynomial_101.BernsteinPosCheck (1/4096 : ℚ) (4069/4096 : ℚ)
  exact sign_101_00

def polynomial_102 : Quartic :=
  ⟨(1 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_102_00 :
    polynomial_102.BernsteinPosCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_102, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_102_00

def entry_102_00 : CachedQuarticSign :=
  ⟨polynomial_102, (0 : ℚ), (1 : ℚ),
    true, .leaf⟩

theorem entry_102_00_checked : entry_102_00.Check := by
  change polynomial_102.BernsteinPosCheck (0 : ℚ) (1 : ℚ)
  exact sign_102_00

def polynomial_103 : Quartic :=
  ⟨(10046146689576360000000000000 : ℚ), (5003763377557379138250604075883 : ℚ), (-178276666500000000000000000 : ℚ), (-12822635882442620861749395924117 : ℚ), (8903198049977123640000000000000 : ℚ)⟩

theorem sign_103_00 :
    polynomial_103.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_103, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_103_00

def entry_103_00 : CachedQuarticSign :=
  ⟨polynomial_103, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_103_00_checked : entry_103_00.Check := by
  change polynomial_103.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_103_00

def polynomial_104 : Quartic :=
  ⟨(101829745360010313127263804000000 : ℚ), (-209485292099994092216407110019111 : ℚ), (268891955032000000000000000000000 : ℚ), (-69385692099994092216407110019111 : ℚ), (-101831790328010313127263804000000 : ℚ)⟩

theorem sign_104_00 :
    polynomial_104.BernsteinNonnegCheck (3005/4096 : ℚ) (1837/2048 : ℚ) := by
  norm_num [polynomial_104, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_104_00

def entry_104_00 : CachedQuarticSign :=
  ⟨polynomial_104, (3005/4096 : ℚ), (1837/2048 : ℚ),
    false, .leaf⟩

theorem entry_104_00_checked : entry_104_00.Check := by
  change polynomial_104.BernsteinNonnegCheck (3005/4096 : ℚ) (1837/2048 : ℚ)
  exact sign_104_00

def polynomial_105 : Quartic :=
  ⟨(1063111 : ℚ), (-16524 : ℚ), (-1063111 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_105_00 :
    polynomial_105.BernsteinPosCheck (1/4096 : ℚ) (127/128 : ℚ) := by
  norm_num [polynomial_105, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_105_00

def entry_105_00 : CachedQuarticSign :=
  ⟨polynomial_105, (1/4096 : ℚ), (127/128 : ℚ),
    true, .leaf⟩

theorem entry_105_00_checked : entry_105_00.Check := by
  change polynomial_105.BernsteinPosCheck (1/4096 : ℚ) (127/128 : ℚ)
  exact sign_105_00

def polynomial_106 : Quartic :=
  ⟨(1064333 : ℚ), (62574 : ℚ), (-1064333 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_106_00 :
    polynomial_106.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_106, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_106_00

def entry_106_00 : CachedQuarticSign :=
  ⟨polynomial_106, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_106_00_checked : entry_106_00.Check := by
  change polynomial_106.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_106_00

def polynomial_107 : Quartic :=
  ⟨(111012177625223879779388441934757 : ℚ), (-206426671384000000000000000000000 : ℚ), (56103273738447759558776883869514 : ℚ), (-206426671384000000000000000000000 : ℚ), (-54908903886776120220611558065243 : ℚ)⟩

theorem sign_107_00 :
    polynomial_107.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ) := by
  norm_num [polynomial_107, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_107_00

def entry_107_00 : CachedQuarticSign :=
  ⟨polynomial_107, (75/4096 : ℚ), (679/2048 : ℚ),
    false, .leaf⟩

theorem entry_107_00_checked : entry_107_00.Check := by
  change polynomial_107.BernsteinNonnegCheck (75/4096 : ℚ) (679/2048 : ℚ)
  exact sign_107_00

def polynomial_108 : Quartic :=
  ⟨(112375885137364935386253321889 : ℚ), (1421137927819024826300462991902 : ℚ), (-224751770274729870772506643778 : ℚ), (-1421137927819024826300462991902 : ℚ), (112375885137364935386253321889 : ℚ)⟩

theorem sign_108_00 :
    polynomial_108.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_108, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_108_00

def entry_108_00 : CachedQuarticSign :=
  ⟨polynomial_108, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_108_00_checked : entry_108_00.Check := by
  change polynomial_108.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_108_00

def polynomial_109 : Quartic :=
  ⟨(1135438180108283028361849016302111623 : ℚ), (1337924420976400000000000000000000000 : ℚ), (-297009981029433943276301967395776754 : ℚ), (1337924420976400000000000000000000000 : ℚ), (-1432448161137716971638150983697888377 : ℚ)⟩

theorem sign_109_00 :
    polynomial_109.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_109, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_109_00

def entry_109_00 : CachedQuarticSign :=
  ⟨polynomial_109, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_109_00_checked : entry_109_00.Check := by
  change polynomial_109.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_109_00

def polynomial_110 : Quartic :=
  ⟨(113825679 : ℚ), (2351647 : ℚ), (999990000 : ℚ), (-1997648353 : ℚ), (886164321 : ℚ)⟩

theorem sign_110_00 :
    polynomial_110.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ) := by
  norm_num [polynomial_110, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_110_00

def entry_110_00 : CachedQuarticSign :=
  ⟨polynomial_110, (0 : ℚ), (1 : ℚ),
    false, .leaf⟩

theorem entry_110_00_checked : entry_110_00.Check := by
  change polynomial_110.BernsteinNonnegCheck (0 : ℚ) (1 : ℚ)
  exact sign_110_00

def polynomial_111 : Quartic :=
  ⟨(11655 : ℚ), (-7604 : ℚ), (-11655 : ℚ), (0 : ℚ), (0 : ℚ)⟩

theorem sign_111_00 :
    polynomial_111.BernsteinPosCheck (1/4096 : ℚ) (743/1024 : ℚ) := by
  norm_num [polynomial_111, Quartic.BernsteinPosCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

#print axioms sign_111_00

def entry_111_00 : CachedQuarticSign :=
  ⟨polynomial_111, (1/4096 : ℚ), (743/1024 : ℚ),
    true, .leaf⟩

theorem entry_111_00_checked : entry_111_00.Check := by
  change polynomial_111.BernsteinPosCheck (1/4096 : ℚ) (743/1024 : ℚ)
  exact sign_111_00

def cache : List CachedQuarticSign :=
  [entry_096_00, entry_097_00, entry_098_00, entry_099_00, entry_100_00, entry_101_00, entry_102_00, entry_103_00, entry_104_00, entry_105_00, entry_106_00, entry_107_00, entry_108_00, entry_109_00, entry_110_00, entry_111_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change entry_096_00.Check ∧ entry_097_00.Check ∧ entry_098_00.Check ∧ entry_099_00.Check ∧ entry_100_00.Check ∧ entry_101_00.Check ∧ entry_102_00.Check ∧ entry_103_00.Check ∧ entry_104_00.Check ∧ entry_105_00.Check ∧ entry_106_00.Check ∧ entry_107_00.Check ∧ entry_108_00.Check ∧ entry_109_00.Check ∧ entry_110_00.Check ∧ entry_111_00.Check ∧ True
  exact ⟨entry_096_00_checked, entry_097_00_checked, entry_098_00_checked, entry_099_00_checked, entry_100_00_checked, entry_101_00_checked, entry_102_00_checked, entry_103_00_checked, entry_104_00_checked, entry_105_00_checked, entry_106_00_checked, entry_107_00_checked, entry_108_00_checked, entry_109_00_checked, entry_110_00_checked, entry_111_00_checked, trivial⟩

#print axioms cache_checked

end ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk06
