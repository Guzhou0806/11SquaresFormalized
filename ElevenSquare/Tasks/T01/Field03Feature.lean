import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

-- Literal feature from field-03, transformed from field coordinates to unit-square coordinates.
def baselineField03Sites : Finset QPoint :=
  {((3801351224026937993380638472577 / 3820000000000000000000000000000), (7429913755929289781925067472577 / 3820000000000000000000000000000)),
    ((2713958513015969924117 / 2500000000000000000000), (18997709591111789468819 / 10000000000000000000000)),
    ((1869077312324257697242572506767 / 1910000000000000000000000000000), (3817124574884991823543842826703 / 1910000000000000000000000000000))}

theorem baseline_field03_sites_card : baselineField03Sites.card = 3 := by
  norm_num [baselineField03Sites, Finset.card_insert_of_notMem]

theorem baseline_field03_majority_capacity {S : ℝ} (P : Packing 11 S)
    (i j : Owner)
    (hi : BaselineMajorityCapture baselineField03Sites 2 (P.squares i))
    (hj : BaselineMajorityCapture baselineField03Sites 2 (P.squares j)) : i = j := by
  exact baseline_majority_unique_owner P baselineField03Sites 2
    (by norm_num [baseline_field03_sites_card]) i j hi hj

theorem baseline_field03_contradiction_of_two_captures {S : ℝ} (P : Packing 11 S)
    (i j : Owner) (hij : i ≠ j)
    (hi : BaselineMajorityCapture baselineField03Sites 2 (P.squares i))
    (hj : BaselineMajorityCapture baselineField03Sites 2 (P.squares j)) : False := by
  exact hij (baseline_field03_majority_capacity P i j hi hj)

end
end ElevenSquare.Tasks.T01
