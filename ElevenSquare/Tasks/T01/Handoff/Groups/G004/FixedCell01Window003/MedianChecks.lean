import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window003.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.G004PairFacetFromCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def referenceAngle : ℚ := (5 / 64)
def coreHalf : ℚ := (529548499998908487 / 1091513000000000000)

theorem facet_check_000 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (referenceAxisQ referenceAngle) := by
  have hlen : 0 < medianTarget.length := by simp [medianTarget]
  refine ⟨medianTarget[0], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet_check_001 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (referenceAxisQ referenceAngle)) := by
  have hlen : 1 < medianTarget.length := by simp [medianTarget]
  refine ⟨medianTarget[1], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet_check_002 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalPerp (referenceAxisQ referenceAngle)) := by
  have hlen : 2 < medianTarget.length := by simp [medianTarget]
  refine ⟨medianTarget[2], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet_check_003 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (rationalPerp (referenceAxisQ referenceAngle))) := by
  have hlen : 3 < medianTarget.length := by simp [medianTarget]
  refine ⟨medianTarget[3], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet_check_004 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site01) := by
  have hlen : 4 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site01) site04 medianTarget[4]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_01_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_005 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site01)) := by
  have hlen : 5 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site01)) site04 medianTarget[5]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_01_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_006 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site02) := by
  have hlen : 6 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site02) site00 medianTarget[6]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_02_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_007 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site02)) := by
  have hlen : 7 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site02)) site02 medianTarget[7]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_02_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_008 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site03) := by
  have hlen : 8 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site03) site03 medianTarget[8]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_03_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_009 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site03)) := by
  have hlen : 9 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site03)) site00 medianTarget[9]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_03_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_010 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site04) := by
  have hlen : 10 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site00 site04) site02 medianTarget[10]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_04_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_011 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site04)) := by
  have hlen : 11 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site00 site04)) site02 medianTarget[11]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_04_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_012 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site01 site02) := by
  have hlen : 12 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site01 site02) site03 medianTarget[12]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_12_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_013 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site01 site02)) := by
  have hlen : 13 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site01 site02)) site03 medianTarget[13]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_12_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_014 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site01 site03) := by
  have hlen : 14 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site01 site03) site03 medianTarget[14]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_13_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_015 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site01 site03)) := by
  have hlen : 15 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site01 site03)) site01 medianTarget[15]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_13_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_016 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site01 site04) := by
  have hlen : 16 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site01 site04) site01 medianTarget[16]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_14_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_017 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site01 site04)) := by
  have hlen : 17 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site01 site04)) site04 medianTarget[17]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_14_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_018 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site02 site03) := by
  have hlen : 18 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site02 site03) site02 medianTarget[18]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_23_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_019 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site02 site03)) := by
  have hlen : 19 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site02 site03)) site03 medianTarget[19]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_23_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_020 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site02 site04) := by
  have hlen : 20 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site02 site04) site00 medianTarget[20]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_24_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_021 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site02 site04)) := by
  have hlen : 21 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site02 site04)) site00 medianTarget[21]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_24_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_022 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site03 site04) := by
  have hlen : 22 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (pairWorldQ site03 site04) site04 medianTarget[22]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_34_pos_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet_check_023 : FixedMedianFacetCheck featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site03 site04)) := by
  have hlen : 23 < medianTarget.length := by simp [medianTarget]
  refine fixed_median_facet_of_cached_lower featureSites 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget
    (rationalNeg (pairWorldQ site03 site04)) site03 medianTarget[23]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g004_pair_34_neg_lower
  all_goals norm_num [featureSites, site00, site01, site02,
    site03, site04, physicalToUnit, medianTarget, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window003
