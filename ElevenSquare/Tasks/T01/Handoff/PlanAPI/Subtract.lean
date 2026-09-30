import ElevenSquare.Tasks.T01.FinitePruning
import ElevenSquare.Tasks.T01.CenterCuts

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- Split a pose row against every facet of a convex forbidden polygon.  The
outside branch of each split is retained; the inside branch proceeds to the
next facet.  Both branches include their common boundary. -/
def outsideRows (r : PoseRow) : Polygon → List PoseRow
  | [] => []
  | h :: hs => cutRow (baselineFlip h) r :: outsideRows (cutRow h r) hs

/-- An input pose lies in one of the retained closed rows or in every closed
halfplane of the forbidden polygon.  This geometric cover needs no numerical
Farkas or arrangement certificate. -/
theorem outsideRows_cover (r : PoseRow) (polygon : Polygon) (q : UnitSquare)
    (hq : r.contains q) :
    RowsContain (outsideRows r polygon) q ∨ q.center ∈ polygon.carrier := by
  induction polygon generalizing r with
  | nil =>
    exact Or.inr (by intro h hh; simp at hh)
  | cons h hs ih =>
    by_cases hh : h.contains q.center
    · have hnext : (cutRow h r).contains q :=
        (cutRow_contains h r q).mpr ⟨hq, hh⟩
      rcases ih (cutRow h r) hnext with hout | hin
      · left
        obtain ⟨out, hm, hcontains⟩ := hout
        exact ⟨out, List.mem_cons_of_mem _ hm, hcontains⟩
      · right
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hh
        · exact hin g hg
    · have hflip : (baselineFlip h).contains q.center :=
        (closed_halfplane_cases h q.center).resolve_left hh
      exact Or.inl ⟨cutRow (baselineFlip h) r, by simp [outsideRows],
        (cutRow_contains (baselineFlip h) r q).mpr ⟨hq, hflip⟩⟩

/-- Apply the same checked forbidden polygon to every predecessor row.  This
state transition recomputes all surviving rows, so archived output rows cannot
be substituted silently. -/
def subtractOneRows (rs : List PoseRow) (piece : ForbiddenPiece) : List PoseRow :=
  rs.flatMap (fun r => outsideRows r piece.polygon)

def SubtractOneCheck (s : PoseState) (i : Owner) (piece : ForbiddenPiece) : Prop :=
  ∀ r ∈ s.rows i, piece.Check s i r

instance (s : PoseState) (i : Owner) (piece : ForbiddenPiece) :
    Decidable (SubtractOneCheck s i piece) := by
  unfold SubtractOneCheck
  infer_instance

/-- Each discarded inside branch has a checked core and a checked convex
difference witness for every polygon vertex, hence cannot host this owner. -/
theorem subtract_one_step (s : PoseState) (i : Owner) (piece : ForbiddenPiece)
    (hc : SubtractOneCheck s i piece) :
    VerifiedStep s (replaceRows s i (subtractOneRows (s.rows i) piece)) := by
  apply VerifiedStep.prunePosewise
  intro q hq
  obtain ⟨r, hr, hrow⟩ := hq
  rcases outsideRows_cover r piece.polygon q hrow with hout | hin
  · left
    obtain ⟨out, hm, hcontains⟩ := hout
    exact ⟨out, List.mem_flatMap.mpr ⟨r, hr, hm⟩, hcontains⟩
  · right
    have hp := hc r hr
    refine ⟨piece.partner, hp.1, rationalHull piece.core, ?_, ?_⟩
    · exact baseline_row_core_checked r piece.core hp.2.2.2 q hrow
    · exact checked_forbidden_polygon (s.owned piece.partner) piece.core
        piece.vertices piece.polygon piece.witnesses hp.2.1 hp.2.2.1 hin

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.outsideRows_cover
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.subtract_one_step
