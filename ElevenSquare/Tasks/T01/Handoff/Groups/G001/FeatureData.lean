import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G001
open ElevenSquare.Pending
noncomputable section

/-- The archived physical coordinates are divided by the rational parent side. -/
def physicalToUnit : ℚ :=
  (382000000000000000000 : ℚ) / 387708359002281417731

/-- The eight exact sites of archived mask 2147, in packet order. -/
def site00 : QPoint := ((14537151717 / 10000000000 : ℚ) / physicalToUnit,
  (9825818383 / 10000000000 : ℚ) / physicalToUnit)
def site01 : QPoint := ((20055000000 / 10000000000 : ℚ) / physicalToUnit,
  (20055000000 / 10000000000 : ℚ) / physicalToUnit)
def site02 : QPoint := ((15343666667 / 10000000000 : ℚ) / physicalToUnit,
  (9868333333 / 10000000000 : ℚ) / physicalToUnit)
def site03 : QPoint := ((15280000000 / 10000000000 : ℚ) / physicalToUnit,
  (9550000000 / 10000000000 : ℚ) / physicalToUnit)
def site04 : QPoint := ((13925204746 / 10000000000 : ℚ) / physicalToUnit,
  (9515724633 / 10000000000 : ℚ) / physicalToUnit)
def site05 : QPoint := ((17614541731 / 10000000000 : ℚ) / physicalToUnit,
  (12398742200 / 10000000000 : ℚ) / physicalToUnit)
def site06 : QPoint := ((18811666667 / 10000000000 : ℚ) / physicalToUnit,
  (18493333333 / 10000000000 : ℚ) / physicalToUnit)
def site07 : QPoint := ((19388333333 / 10000000000 : ℚ) / physicalToUnit,
  (18493333333 / 10000000000 : ℚ) / physicalToUnit)
def featureA : Finset QPoint := {site00, site02, site03, site04, site05}
def featureB : Finset QPoint := {site01, site06, site07}

theorem featureA_card : featureA.card = 5 := by
  norm_num [featureA, site00, site02, site03, site04, site05,
    physicalToUnit, Finset.card_insert_of_notMem]

theorem featureB_card : featureB.card = 3 := by
  norm_num [featureB, site01, site06, site07, physicalToUnit,
    Finset.card_insert_of_notMem]

def Captures (f : Fin 2) (q : UnitSquare) : Prop :=
  if f = 0 then BaselineMajorityCapture featureA 3 q
  else BaselineMajorityCapture featureB 2 q

theorem same_feature_unique {S : ℝ} (P : Packing 11 S)
    (f : Fin 2) (i j : Owner)
    (hi : Captures f (P.squares i)) (hj : Captures f (P.squares j)) : i = j := by
  fin_cases f
  · exact baseline_majority_unique_owner P featureA 3
      (by rw [featureA_card]) i j hi hj
  · exact baseline_majority_unique_owner P featureB 2
      (by rw [featureB_card]) i j hi hj

/-- Three distinct cell owners cannot all capture one of two capacity-one features. -/
theorem three_captures_impossible {S : ℝ} (P : Packing 11 S)
    (owners : Fin 3 → Owner) (hinj : Function.Injective owners)
    (hcap : ∀ j : Fin 3,
      BaselineMajorityCapture featureA 3 (P.squares (owners j)) ∨
      BaselineMajorityCapture featureB 2 (P.squares (owners j))) : False := by
  classical
  have hex : ∀ j : Fin 3, ∃ f : Fin 2, Captures f (P.squares (owners j)) := by
    intro j
    rcases hcap j with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  choose assigned hassigned using hex
  have ha : Function.Injective assigned := by
    intro j k heq
    apply hinj
    exact same_feature_unique P (assigned j) (owners j) (owners k)
      (hassigned j) (heq ▸ hassigned k)
  have hc : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_injective assigned ha
  norm_num at hc

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G001

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G001.three_captures_impossible
