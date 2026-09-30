import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G041
open ElevenSquare.Pending
noncomputable section

/-- Group 041, mask 1294. Finite witness data from the archived proposal;
    no continuous capture claim is encoded here. -/

def physicalToUnit : ℚ := (382000000000000000000 : ℚ) / 387708359002281417731

def site00 : QPoint := ((23014971255 / 10000000000 : ℚ) / physicalToUnit,
  (28439535457 / 10000000000 : ℚ) / physicalToUnit)

def site01 : QPoint := ((18515725490 / 10000000000 : ℚ) / physicalToUnit,
  (9978081248 / 10000000000 : ℚ) / physicalToUnit)

def site02 : QPoint := ((28841000000 / 10000000000 : ℚ) / physicalToUnit,
  (18272333333 / 10000000000 : ℚ) / physicalToUnit)

def site03 : QPoint := ((29350333333 / 10000000000 : ℚ) / physicalToUnit,
  (18527000000 / 10000000000 : ℚ) / physicalToUnit)

def site04 : QPoint := ((23853848283 / 10000000000 : ℚ) / physicalToUnit,
  (28374181617 / 10000000000 : ℚ) / physicalToUnit)

def site05 : QPoint := ((18696636766 / 10000000000 : ℚ) / physicalToUnit,
  (9783303433 / 10000000000 : ℚ) / physicalToUnit)

def site06 : QPoint := ((20532500000 / 10000000000 : ℚ) / physicalToUnit,
  (25785000000 / 10000000000 : ℚ) / physicalToUnit)

def site07 : QPoint := ((29605000000 / 10000000000 : ℚ) / physicalToUnit,
  (19100000000 / 10000000000 : ℚ) / physicalToUnit)

def site08 : QPoint := ((11842000000 / 10000000000 : ℚ) / physicalToUnit,
  (17190000000 / 10000000000 : ℚ) / physicalToUnit)

def site09 : QPoint := ((29032000000 / 10000000000 : ℚ) / physicalToUnit,
  (27504000000 / 10000000000 : ℚ) / physicalToUnit)

def site10 : QPoint := ((29796000000 / 10000000000 : ℚ) / physicalToUnit,
  (17572000000 / 10000000000 : ℚ) / physicalToUnit)

def site11 : QPoint := ((19075319138 / 10000000000 : ℚ) / physicalToUnit,
  (19075319138 / 10000000000 : ℚ) / physicalToUnit)

def site12 : QPoint := ((21965643573 / 10000000000 : ℚ) / physicalToUnit,
  (28410524300 / 10000000000 : ℚ) / physicalToUnit)

def site13 : QPoint := ((11842000000 / 10000000000 : ℚ) / physicalToUnit,
  (16808000000 / 10000000000 : ℚ) / physicalToUnit)

def site14 : QPoint := ((21392000000 / 10000000000 : ℚ) / physicalToUnit,
  (26358000000 / 10000000000 : ℚ) / physicalToUnit)

def site15 : QPoint := ((28393675409 / 10000000000 : ℚ) / physicalToUnit,
  (18559107495 / 10000000000 : ℚ) / physicalToUnit)

def site16 : QPoint := ((9543188187 / 10000000000 : ℚ) / physicalToUnit,
  (13802593804 / 10000000000 : ℚ) / physicalToUnit)

def site17 : QPoint := ((29414000000 / 10000000000 : ℚ) / physicalToUnit,
  (27504000000 / 10000000000 : ℚ) / physicalToUnit)

def site18 : QPoint := ((8786000000 / 10000000000 : ℚ) / physicalToUnit,
  (14134000000 / 10000000000 : ℚ) / physicalToUnit)

def site19 : QPoint := ((18485628777 / 10000000000 : ℚ) / physicalToUnit,
  (9835875164 / 10000000000 : ℚ) / physicalToUnit)

def site20 : QPoint := ((28694887290 / 10000000000 : ℚ) / physicalToUnit,
  (28348696869 / 10000000000 : ℚ) / physicalToUnit)

def site21 : QPoint := ((28375472143 / 10000000000 : ℚ) / physicalToUnit,
  (28347307480 / 10000000000 : ℚ) / physicalToUnit)

def site22 : QPoint := ((9844569529 / 10000000000 : ℚ) / physicalToUnit,
  (17795948690 / 10000000000 : ℚ) / physicalToUnit)

def site23 : QPoint := ((29998606885 / 10000000000 : ℚ) / physicalToUnit,
  (28466907378 / 10000000000 : ℚ) / physicalToUnit)


/-- Feature 0: archived physical-feature index 282. -/
def feature0 : Finset QPoint := {site01, site05, site19}

theorem feature0_card : feature0.card = 3 := by
  norm_num [feature0, site01, site05, site19, physicalToUnit, Finset.card_insert_of_not_mem]

theorem feature0_majority_capacity {S : ℝ} (P : Packing 11 S)
    (left right : Owner)
    (hl : BaselineMajorityCapture feature0 2 (P.squares left))
    (hr : BaselineMajorityCapture feature0 2 (P.squares right)) :
    left = right := by
  exact baseline_majority_unique_owner P feature0 2
    (by rw [feature0_card]) left right hl hr


/-- Feature 1: archived physical-feature index 349. -/
def feature1 : Finset QPoint := {site00, site04, site06, site12, site14}

theorem feature1_card : feature1.card = 5 := by
  norm_num [feature1, site00, site04, site06, site12, site14, physicalToUnit, Finset.card_insert_of_not_mem]

theorem feature1_majority_capacity {S : ℝ} (P : Packing 11 S)
    (left right : Owner)
    (hl : BaselineMajorityCapture feature1 3 (P.squares left))
    (hr : BaselineMajorityCapture feature1 3 (P.squares right)) :
    left = right := by
  exact baseline_majority_unique_owner P feature1 3
    (by rw [feature1_card]) left right hl hr


/-- Feature 2: archived physical-feature index 368. -/
def feature2 : Finset QPoint := {site08, site13, site16, site18, site22}

theorem feature2_card : feature2.card = 5 := by
  norm_num [feature2, site08, site13, site16, site18, site22, physicalToUnit, Finset.card_insert_of_not_mem]

theorem feature2_majority_capacity {S : ℝ} (P : Packing 11 S)
    (left right : Owner)
    (hl : BaselineMajorityCapture feature2 3 (P.squares left))
    (hr : BaselineMajorityCapture feature2 3 (P.squares right)) :
    left = right := by
  exact baseline_majority_unique_owner P feature2 3
    (by rw [feature2_card]) left right hl hr


/-- Feature 3: archived physical-feature index 458. -/
def feature3 : Finset QPoint := {site02, site03, site07, site10, site15}

theorem feature3_card : feature3.card = 5 := by
  norm_num [feature3, site02, site03, site07, site10, site15, physicalToUnit, Finset.card_insert_of_not_mem]

theorem feature3_majority_capacity {S : ℝ} (P : Packing 11 S)
    (left right : Owner)
    (hl : BaselineMajorityCapture feature3 3 (P.squares left))
    (hr : BaselineMajorityCapture feature3 3 (P.squares right)) :
    left = right := by
  exact baseline_majority_unique_owner P feature3 3
    (by rw [feature3_card]) left right hl hr


/-- Feature 4: archived physical-feature index 483. -/
def feature4 : Finset QPoint := {site09, site17, site20, site21, site23}

theorem feature4_card : feature4.card = 5 := by
  norm_num [feature4, site09, site17, site20, site21, site23, physicalToUnit, Finset.card_insert_of_not_mem]

theorem feature4_majority_capacity {S : ℝ} (P : Packing 11 S)
    (left right : Owner)
    (hl : BaselineMajorityCapture feature4 3 (P.squares left))
    (hr : BaselineMajorityCapture feature4 3 (P.squares right)) :
    left = right := by
  exact baseline_majority_unique_owner P feature4 3
    (by rw [feature4_card]) left right hl hr


def featureAt : Fin 5 → Finset QPoint :=
  ![feature0, feature1, feature2, feature3, feature4]

def thresholdAt : Fin 5 → ℕ := ![2, 3, 3, 3, 3]

theorem featureAt_majority_capacity {S : ℝ} (P : Packing 11 S)
    (j : Fin 5) (left right : Owner)
    (hl : BaselineMajorityCapture (featureAt j) (thresholdAt j) (P.squares left))
    (hr : BaselineMajorityCapture (featureAt j) (thresholdAt j) (P.squares right)) :
    left = right := by
  fin_cases j
  · exact feature0_majority_capacity P left right hl hr
  · exact feature1_majority_capacity P left right hl hr
  · exact feature2_majority_capacity P left right hl hr
  · exact feature3_majority_capacity P left right hl hr
  · exact feature4_majority_capacity P left right hl hr

/-- Seven positive physical cells in the archived mask, in sorted owner order.
    The capture hypotheses are the missing continuous geometry checks. -/
def positiveOwner : Fin 7 → Owner := ![1, 3, 4, 5, 7, 8, 10]

theorem positiveOwner_injective : Function.Injective positiveOwner := by
  decide

theorem impossible_of_positive_captures {S : ℝ} (P : Packing 11 S)
    (assigned : Fin 7 → Fin 5)
    (captures : ∀ j : Fin 7,
      BaselineMajorityCapture (featureAt (assigned j)) (thresholdAt (assigned j))
        (P.squares (positiveOwner j))) : False := by
  have hinj : Function.Injective assigned := by
    intro j k heq
    have hk := captures k
    rw [← heq] at hk
    exact positiveOwner_injective
      (featureAt_majority_capacity P (assigned j) (positiveOwner j)
        (positiveOwner k) (captures j) hk)
  have hcard : Fintype.card (Fin 7) ≤ Fintype.card (Fin 5) :=
    Fintype.card_le_of_injective assigned hinj
  norm_num at hcard

theorem impossible_of_positive_coverage {S : ℝ} (P : Packing 11 S)
    (captures : ∀ j : Fin 7, ∃ feature : Fin 5,
      BaselineMajorityCapture (featureAt feature) (thresholdAt feature)
        (P.squares (positiveOwner j))) : False := by
  choose assigned hassigned using captures
  exact impossible_of_positive_captures P assigned hassigned

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G041
