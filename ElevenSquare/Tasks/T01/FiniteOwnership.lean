import ElevenSquare.Tasks.T01.ConvexWitnesses
import ElevenSquare.Tasks.T01.DirectOwnership

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

instance poseRowDecidableEq : DecidableEq PoseRow := fun a b =>
  decidable_of_iff (a.lo = b.lo ∧ a.hi = b.hi ∧ a.centers = b.centers) (by
    cases a
    cases b
    simp only [PoseRow.mk.injEq])

def HullVerticesCheck (source output : List QPoint) (ws : List HullWitness) : Prop :=
  output.length = ws.length ∧
  ∀ pw ∈ output.zip ws, pw.2.Valid source ∧ pw.1 = pw.2.eval source

instance (source output : List QPoint) (ws : List HullWitness) :
    Decidable (HullVerticesCheck source output ws) := by
  unfold HullVerticesCheck
  infer_instance

theorem hull_vertices_checked (source output : List QPoint) (ws : List HullWitness)
    (hc : HullVerticesCheck source output ws) :
    ∀ p ∈ output, realPoint p ∈ rationalHull source := by
  induction output generalizing ws with
  | nil => simp
  | cons p ps ih =>
    cases ws with
    | nil => simp [HullVerticesCheck] at hc
    | cons w ws =>
      have hw := hc.2 (p,w) (by simp)
      dsimp only [Prod.fst, Prod.snd] at hw
      have ht : HullVerticesCheck source ps ws := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro x hx
        exact hc.2 x (by simp [hx])
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hw.2]
        exact hullWitness_sound source w hw.1
      · exact ih ws ht v hv

/-- Replace the owned hull by exactly the retained vertices in the archive.
Each retained vertex has a checked convex witness in old or freshly owned points. -/
structure OwnershipCertificate where
  fresh : List QPoint
  output : List QPoint
  rows : List (PoseRow × List QPoint)
  witnesses : List HullWitness

def OwnershipCertificate.Check (s : PoseState) (i : Owner)
    (c : OwnershipCertificate) : Prop :=
  c.rows.map Prod.fst = s.rows i ∧
  (∀ item ∈ c.rows, ∀ p ∈ c.fresh, DirectPointCheck item.1 item.2 p) ∧
  HullVerticesCheck (s.owned i ++ c.fresh) c.output c.witnesses

instance ownershipCertificateCheckDecidable (s : PoseState) (i : Owner) (c : OwnershipCertificate) :
    Decidable (c.Check s i) := by
  unfold OwnershipCertificate.Check
  infer_instance

theorem checked_ownership_step (s : PoseState) (i : Owner)
    (c : OwnershipCertificate) (hc : c.Check s i) :
    VerifiedStep s (replaceHull s i c.output) := by
  apply VerifiedStep.promoteOwned
  intro q hq hold p hp
  have hall : rationalHull (s.owned i ++ c.fresh) ⊆ {v | OpenSquare q v} := by
    apply hull_owned_of_vertices
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hold (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
    · obtain ⟨r, hr, hcontains⟩ := hq
      rw [← hc.1] at hr
      obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
      exact directPointCheck_sound item.1 item.2 v (hc.2.1 item hm v hv) q hcontains
  exact hall (hull_vertices_checked _ _ _ hc.2.2 p hp)

end
end ElevenSquare.Tasks.T01
