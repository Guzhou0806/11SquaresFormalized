import ElevenSquare.Tasks.T01.Core031
import Mathlib.Tactic.FinCases

/-! All 32 literal common cores, with kernel-checked strict containment. -/

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

def baselineGenericCore : Fin 32 → List QPoint :=
  ![baselineCore000, baselineCore001, baselineCore002, baselineCore003, baselineCore004, baselineCore005, baselineCore006, baselineCore007, baselineCore008, baselineCore009, baselineCore010, baselineCore011, baselineCore012, baselineCore013, baselineCore014, baselineCore015, baselineCore016, baselineCore017, baselineCore018, baselineCore019, baselineCore020, baselineCore021, baselineCore022, baselineCore023, baselineCore024, baselineCore025, baselineCore026, baselineCore027, baselineCore028, baselineCore029, baselineCore030, baselineCore031]

theorem baseline_generic_core_checked (i : Fin 32) :
    ∀ v ∈ baselineGenericCore i,
      BaselineCoreVertexCheck v ((i.val:ℚ)/32) (((i.val:ℚ)+1)/32) := by
  fin_cases i
  · convert baselineCore000_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore001_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore002_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore003_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore004_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore005_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore006_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore007_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore008_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore009_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore010_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore011_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore012_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore013_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore014_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore015_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore016_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore017_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore018_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore019_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore020_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore021_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore022_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore023_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore024_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore025_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore026_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore027_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore028_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore029_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore030_checked using 1; norm_num [baselineGenericCore]
  · convert baselineCore031_checked using 1; norm_num [baselineGenericCore]

theorem baseline_generic_core_fits (i : Fin 32) (q : UnitSquare) (t : ℝ)
    (hl : (((i.val:ℚ)/32):ℝ) ≤ t) (hu : t ≤ ((((i.val:ℚ)+1)/32):ℝ))
    (hq : q.axis = chartAxis t) : CoreFits (rationalHull (baselineGenericCore i)) q := by
  apply baseline_common_core_hull
  intro v hv
  exact baseline_core_vertex_check_sound q v _ _
    (baseline_generic_core_checked i v hv) t (by exact_mod_cast hl) (by exact_mod_cast hu) hq

end
end ElevenSquare.Tasks.T01
