import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061.MedianChecks0
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.G005PairMedianCacheB
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.G004PairFacetFromCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem facet1_check_000 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (referenceAxisQ referenceAngle) := by
  have hlen : 0 < medianTarget1.length := by simp [medianTarget1]
  refine ⟨medianTarget1[0], @List.getElem_mem _ _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet1_check_001 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (referenceAxisQ referenceAngle)) := by
  have hlen : 1 < medianTarget1.length := by simp [medianTarget1]
  refine ⟨medianTarget1[1], @List.getElem_mem _ _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet1_check_002 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalPerp (referenceAxisQ referenceAngle)) := by
  have hlen : 2 < medianTarget1.length := by simp [medianTarget1]
  refine ⟨medianTarget1[2], @List.getElem_mem _ _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet1_check_003 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (rationalPerp (referenceAxisQ referenceAngle))) := by
  have hlen : 3 < medianTarget1.length := by simp [medianTarget1]
  refine ⟨medianTarget1[3], @List.getElem_mem _ _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet1_check_004 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (pairWorldQ site02 site06) := by
  have hlen : 4 < medianTarget1.length := by simp [medianTarget1]
  refine fixed_median_facet_of_cached_lower featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (pairWorldQ site02 site06) site02 medianTarget1[4]
    (@List.getElem_mem _ _ _ hlen) ?_ ?_ ?_
    g005_b_pair_26_pos_lower
  all_goals norm_num [featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet1_check_005 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (pairWorldQ site02 site06)) := by
  have hlen : 5 < medianTarget1.length := by simp [medianTarget1]
  refine fixed_median_facet_of_cached_lower featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (pairWorldQ site02 site06)) site02 medianTarget1[5]
    (@List.getElem_mem _ _ _ hlen) ?_ ?_ ?_
    g005_b_pair_26_neg_lower
  all_goals norm_num [featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet1_check_006 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (pairWorldQ site02 site07) := by
  have hlen : 6 < medianTarget1.length := by simp [medianTarget1]
  refine fixed_median_facet_of_cached_lower featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (pairWorldQ site02 site07) site02 medianTarget1[6]
    (@List.getElem_mem _ _ _ hlen) ?_ ?_ ?_
    g005_b_pair_27_pos_lower
  all_goals norm_num [featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet1_check_007 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (pairWorldQ site02 site07)) := by
  have hlen : 7 < medianTarget1.length := by simp [medianTarget1]
  refine fixed_median_facet_of_cached_lower featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (pairWorldQ site02 site07)) site02 medianTarget1[7]
    (@List.getElem_mem _ _ _ hlen) ?_ ?_ ?_
    g005_b_pair_27_neg_lower
  all_goals norm_num [featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet1_check_008 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (pairWorldQ site06 site07) := by
  have hlen : 8 < medianTarget1.length := by simp [medianTarget1]
  refine fixed_median_facet_of_cached_lower featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (pairWorldQ site06 site07) site06 medianTarget1[8]
    (@List.getElem_mem _ _ _ hlen) ?_ ?_ ?_
    g005_b_pair_67_pos_lower
  all_goals norm_num [featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet1_check_009 : FixedMedianFacetCheck featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (pairWorldQ site06 site07)) := by
  have hlen : 9 < medianTarget1.length := by simp [medianTarget1]
  refine fixed_median_facet_of_cached_lower featureB 2
    (referenceAxisQ referenceAngle) coreHalf medianTarget1
    (rationalNeg (pairWorldQ site06 site07)) site06 medianTarget1[9]
    (@List.getElem_mem _ _ _ hlen) ?_ ?_ ?_
    g005_b_pair_67_neg_lower
  all_goals norm_num [featureB, site02, site06, site07,
    physicalToUnit, medianTarget1, referenceAngle, coreHalf,
    rationalCoreSupport, localNormalQ, rationalDot, rationalPerp,
    rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061
