import ElevenSquare.Tasks.T01.Field03Cell04Prefix010

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Append one closed interval to a previously established closed prefix. The
shared endpoint belongs to both premises. -/
theorem field03_closed_interval_append (M : ℝ → Prop) (mid hi : ℝ)
    (hprefix : ∀ t, 0 ≤ t → t ≤ mid → M t)
    (hrow : ∀ t, mid ≤ t → t ≤ hi → M t)
    (t : ℝ) (ht0 : 0 ≤ t) (htop : t ≤ hi) : M t := by
  by_cases hmid : t ≤ mid
  · exact hprefix t ht0 hmid
  · exact hrow t (le_of_lt (lt_of_not_ge hmid)) htop

end
end ElevenSquare.Tasks.T01
