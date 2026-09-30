import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFixedFacet
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FeatureData

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.Groups.G005
noncomputable section

/-- A pair-normal projects two sites equally, giving the middle support value
    for the three-site feature in either direction. -/
theorem g005_b_pair_26_pos_lower :
    MedianLowerBound featureB 2 (rationalDot (pairWorldQ site02 site06))
      (rationalDot (pairWorldQ site02 site06) site02) := by
  norm_num [MedianLowerBound, Finset.filter_insert, Finset.filter_singleton,
    featureB, site02, site06, site07, physicalToUnit, rationalDot,
    rationalNeg, pairWorldQ]

theorem g005_b_pair_26_neg_lower :
    MedianLowerBound featureB 2
      (rationalDot (rationalNeg (pairWorldQ site02 site06)))
      (rationalDot (rationalNeg (pairWorldQ site02 site06)) site02) := by
  norm_num [MedianLowerBound, Finset.filter_insert, Finset.filter_singleton,
    featureB, site02, site06, site07, physicalToUnit, rationalDot,
    rationalNeg, pairWorldQ]

theorem g005_b_pair_27_pos_lower :
    MedianLowerBound featureB 2 (rationalDot (pairWorldQ site02 site07))
      (rationalDot (pairWorldQ site02 site07) site02) := by
  norm_num [MedianLowerBound, Finset.filter_insert, Finset.filter_singleton,
    featureB, site02, site06, site07, physicalToUnit, rationalDot,
    rationalNeg, pairWorldQ]

theorem g005_b_pair_27_neg_lower :
    MedianLowerBound featureB 2
      (rationalDot (rationalNeg (pairWorldQ site02 site07)))
      (rationalDot (rationalNeg (pairWorldQ site02 site07)) site02) := by
  norm_num [MedianLowerBound, Finset.filter_insert, Finset.filter_singleton,
    featureB, site02, site06, site07, physicalToUnit, rationalDot,
    rationalNeg, pairWorldQ]

theorem g005_b_pair_67_pos_lower :
    MedianLowerBound featureB 2 (rationalDot (pairWorldQ site06 site07))
      (rationalDot (pairWorldQ site06 site07) site06) := by
  norm_num [MedianLowerBound, Finset.filter_insert, Finset.filter_singleton,
    featureB, site02, site06, site07, physicalToUnit, rationalDot,
    rationalNeg, pairWorldQ]

theorem g005_b_pair_67_neg_lower :
    MedianLowerBound featureB 2
      (rationalDot (rationalNeg (pairWorldQ site06 site07)))
      (rationalDot (rationalNeg (pairWorldQ site06 site07)) site06) := by
  norm_num [MedianLowerBound, Finset.filter_insert, Finset.filter_singleton,
    featureB, site02, site06, site07, physicalToUnit, rationalDot,
    rationalNeg, pairWorldQ]

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_b_pair_26_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_b_pair_26_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_b_pair_27_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_b_pair_27_neg_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_b_pair_67_pos_lower
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.g005_b_pair_67_neg_lower
