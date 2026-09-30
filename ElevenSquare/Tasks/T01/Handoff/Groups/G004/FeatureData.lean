import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004
open ElevenSquare.Pending
noncomputable section

/-- The archived physical coordinates use a square of side `191/50 / coverCap`.
    Lean coordinates use unit squares. -/
def physicalToUnit : ℚ :=
  (382000000000000000000 : ℚ) / 387708359002281417731

/-- Archived physical-feature 931. -/
def site00 : QPoint :=
  ((19100000000 / 10000000000 : ℚ) / physicalToUnit,
   (5730000000 / 10000000000 : ℚ) / physicalToUnit)
def site01 : QPoint :=
  ((17910340775 / 10000000000 : ℚ) / physicalToUnit,
   (9857037040 / 10000000000 : ℚ) / physicalToUnit)
def site02 : QPoint :=
  ((20289659225 / 10000000000 : ℚ) / physicalToUnit,
   (9857037040 / 10000000000 : ℚ) / physicalToUnit)
def site03 : QPoint :=
  ((19259886387 / 10000000000 : ℚ) / physicalToUnit,
   (9793611581 / 10000000000 : ℚ) / physicalToUnit)
def site04 : QPoint :=
  ((19708867058 / 10000000000 : ℚ) / physicalToUnit,
   (6911209005 / 10000000000 : ℚ) / physicalToUnit)

def featureSites : Finset QPoint := {site00, site01, site02, site03, site04}

theorem featureSites_card : featureSites.card = 5 := by
  norm_num [featureSites, site00, site01, site02, site03, site04,
    physicalToUnit, Finset.card_insert_of_not_mem]

theorem feature_capacity {S : ℝ} (P : Packing 11 S)
    (left right : Owner)
    (hl : BaselineMajorityCapture featureSites 3 (P.squares left))
    (hr : BaselineMajorityCapture featureSites 3 (P.squares right)) :
    left = right := by
  exact baseline_majority_unique_owner P featureSites 3
    (by rw [featureSites_card]) left right hl hr

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.feature_capacity
