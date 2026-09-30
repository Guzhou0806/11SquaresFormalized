import ElevenSquare.Tasks.T01.Seeds

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

theorem baseline_physical_site_owned (q : UnitSquare) (cell : Fin 16)
    (hcell : ClosedCell cell (normalizeCenter q.center)) :
    OpenSquare q (realPoint (baselinePhysicalSite cell)) := by
  apply open_of_normSq_lt
  exact (baseline_site_distance_bound cell q.center hcell).trans (by norm_num)

end
end ElevenSquare.Tasks.T01
