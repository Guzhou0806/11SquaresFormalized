import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.G005PairMedianCache
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.G004PairFacetFromCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def referenceAngle : ℚ := (63 / 128)
def coreHalf : ℚ := (51462560499895784511 / 104215489000000000000)

theorem facet0_check_000 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (referenceAxisQ referenceAngle) := by
  have hlen : 0 < medianTarget0.length := by simp [medianTarget0]
  refine ⟨medianTarget0[0], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet0_check_001 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (referenceAxisQ referenceAngle)) := by
  have hlen : 1 < medianTarget0.length := by simp [medianTarget0]
  refine ⟨medianTarget0[1], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet0_check_002 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalPerp (referenceAxisQ referenceAngle)) := by
  have hlen : 2 < medianTarget0.length := by simp [medianTarget0]
  refine ⟨medianTarget0[2], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet0_check_003 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (rationalPerp (referenceAxisQ referenceAngle))) := by
  have hlen : 3 < medianTarget0.length := by simp [medianTarget0]
  refine ⟨medianTarget0[3], List.getElem_mem _ _ hlen, ?_, ?_, ?_⟩
  all_goals norm_num [MedianLowerBound, Finset.filter_insert,
    Finset.filter_singleton, featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]

theorem facet0_check_004 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site01) := by
  have hlen : 4 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site01) site01 medianTarget0[4]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_01_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_005 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site01)) := by
  have hlen : 5 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site01)) site00 medianTarget0[5]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_01_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_006 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site03) := by
  have hlen : 6 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site03) site00 medianTarget0[6]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_03_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_007 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site03)) := by
  have hlen : 7 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site03)) site03 medianTarget0[7]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_03_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_008 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site04) := by
  have hlen : 8 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site04) site04 medianTarget0[8]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_04_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_009 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site04)) := by
  have hlen : 9 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site04)) site00 medianTarget0[9]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_04_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_010 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site05) := by
  have hlen : 10 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site00 site05) site00 medianTarget0[10]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_05_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_011 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site05)) := by
  have hlen : 11 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site00 site05)) site05 medianTarget0[11]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_05_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_012 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site01 site03) := by
  have hlen : 12 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site01 site03) site03 medianTarget0[12]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_13_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_013 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site01 site03)) := by
  have hlen : 13 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site01 site03)) site01 medianTarget0[13]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_13_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_014 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site01 site04) := by
  have hlen : 14 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site01 site04) site01 medianTarget0[14]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_14_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_015 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site01 site04)) := by
  have hlen : 15 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site01 site04)) site04 medianTarget0[15]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_14_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_016 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site01 site05) := by
  have hlen : 16 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site01 site05) site05 medianTarget0[16]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_15_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_017 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site01 site05)) := by
  have hlen : 17 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site01 site05)) site01 medianTarget0[17]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_15_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_018 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site03 site04) := by
  have hlen : 18 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site03 site04) site01 medianTarget0[18]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_34_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_019 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site03 site04)) := by
  have hlen : 19 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site03 site04)) site01 medianTarget0[19]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_34_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_020 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site03 site05) := by
  have hlen : 20 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site03 site05) site01 medianTarget0[20]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_35_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_021 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site03 site05)) := by
  have hlen : 21 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site03 site05)) site01 medianTarget0[21]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_35_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_022 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site04 site05) := by
  have hlen : 22 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (pairWorldQ site04 site05) site00 medianTarget0[22]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_45_pos_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

theorem facet0_check_023 : FixedMedianFacetCheck featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site04 site05)) := by
  have hlen : 23 < medianTarget0.length := by simp [medianTarget0]
  refine fixed_median_facet_of_cached_lower featureA 3
    (referenceAxisQ referenceAngle) coreHalf medianTarget0
    (rationalNeg (pairWorldQ site04 site05)) site00 medianTarget0[23]
    (List.getElem_mem _ _ hlen) ?_ ?_ ?_
    g005_pair_45_neg_lower
  all_goals norm_num [featureA, site00, site01, site03,
    site04, site05, physicalToUnit, medianTarget0, referenceAngle,
    coreHalf, rationalCoreSupport, localNormalQ, rationalDot,
    rationalPerp, rationalNeg, referenceAxisQ, pairWorldQ]
  all_goals repeat first
    | rw [abs_of_nonneg (by norm_num)]
    | rw [abs_of_nonpos (by norm_num)]
  all_goals norm_num

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window061
