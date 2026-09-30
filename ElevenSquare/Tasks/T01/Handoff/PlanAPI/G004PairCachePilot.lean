import ElevenSquare.Tasks.T01.Handoff.PlanAPI.G004PairFacetFromCache
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window000.Data

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01.Handoff.Groups.G004
open ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window000
noncomputable section

private def referenceAngle : ℚ := 1 / 128
private def coreHalf : ℚ := 8192499999983361 / 16639000000000000

theorem g004_pair_cache_pilot : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site01) := by
  have hlen : 4 < medianTarget.length := by simp [medianTarget]
  apply fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site01) site04 medianTarget[4]
    (List.getElem_mem _ _ hlen)
  · norm_num [medianTarget, pairWorldQ, site00, site01,
      physicalToUnit]
  · norm_num [medianTarget, pairWorldQ, site00, site01,
      physicalToUnit]
  · norm_num [medianTarget, coreHalf, referenceAngle,
      rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
      referenceAxisQ, pairWorldQ, site00, site01, site04, physicalToUnit]
    rw [abs_of_pos (show (0:ℚ) <
      329153737662333091222397536405119 / 782383750000000000000000000000000 by norm_num),
      abs_of_pos (show (0:ℚ) <
      1429377248107062521442859575835697 / 12518140000000000000000000000000000 by norm_num)]
    norm_num
  · exact g004_pair_01_pos_lower

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g004_pair_cache_pilot
