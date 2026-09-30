import ElevenSquare.Tasks.T03.FiniteConvex

namespace ElevenSquare.Pending.T03
noncomputable section

def differenceCheck (ks qs : List QPoint) (k v p : QPoint) : Bool :=
  decide (k ∈ ks ∧ v ∈ qs ∧ p=k-v)

theorem differenceCheck_sound (ks qs : List QPoint) (k v p : QPoint)
    (h : differenceCheck ks qs k v p = true) :
    realPoint p ∈ forbiddenCenters (rationalHull ks) (rationalHull qs) := by
  obtain ⟨hk,hv,he⟩ := of_decide_eq_true h
  exact rational_difference_forbidden ks qs k v p hk hv he

end
end ElevenSquare.Pending.T03
