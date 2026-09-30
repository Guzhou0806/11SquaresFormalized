import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending
noncomputable section

/-- The original field coordinates are divided by the rational parent side. -/
def physicalToUnit : ℚ := (382000000000000000000 : ℚ) / 387708359002281417731

def point : QPoint :=
  ((19100000000 / 10000000000 : ℚ) / physicalToUnit,
   (22983666667 / 10000000000 : ℚ) / physicalToUnit)

def site0 : QPoint :=
  ((17954000000 / 10000000000 : ℚ) / physicalToUnit,
   (18336000000 / 10000000000 : ℚ) / physicalToUnit)

def site1 : QPoint :=
  ((15910052884 / 10000000000 : ℚ) / physicalToUnit,
   (17635608117 / 10000000000 : ℚ) / physicalToUnit)

def site2 : QPoint :=
  ((17635608117 / 10000000000 : ℚ) / physicalToUnit,
   (15910052884 / 10000000000 : ℚ) / physicalToUnit)

def sites : Finset QPoint := {site0, site1, site2}

theorem sites_card : sites.card = 3 := by
  norm_num [sites, site0, site1, site2, physicalToUnit,
    Finset.card_insert_of_not_mem]

def Captures (f : Fin 2) (q : UnitSquare) : Prop :=
  if f = 0 then OpenSquare q (realPoint point) else BaselineMajorityCapture sites 2 q

theorem same_feature_unique {S : ℝ} (P : Packing 11 S)
    (f : Fin 2) (i j : Owner)
    (hi : Captures f (P.squares i)) (hj : Captures f (P.squares j)) : i = j := by
  fin_cases f
  · by_contra hij
    exact P.interior_disjoint i j hij (realPoint point) ⟨hi, hj⟩
  · exact baseline_majority_unique_owner P sites 2 (by rw [sites_card]) i j hi hj

/-- The one singleton point and one three-site majority feature have capacity two.
    The three required physical cells therefore contradict pairwise distinct owners,
    once their continuous capture hypotheses have been supplied. -/
theorem three_captures_impossible {S : ℝ} (P : Packing 11 S)
    (owners : Fin 3 → Owner) (hinj : Function.Injective owners)
    (hcap : ∀ j : Fin 3,
      OpenSquare (P.squares (owners j)) (realPoint point) ∨
        BaselineMajorityCapture sites 2 (P.squares (owners j))) : False := by
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
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.three_captures_impossible
