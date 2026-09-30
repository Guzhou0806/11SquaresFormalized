import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicGuardedCover
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicStrictGuardedCover

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A finite rational partition of the orientation chart. Each leaf has its
own moving center cover and target polygons. This keeps angle subdivision
separate from the geometric BSP in a fixed interval. -/
inductive SymbolicIntervalCoverCertificate where
  | leaf (targets : List (List SymbolicFacet))
      (cover : SymbolicCoverCertificate)
  | signSplit (guard : SymbolicQuadratic)
      (positiveTargets negativeTargets : List (List SymbolicFacet))
      (positiveCover negativeCover : GuardedSymbolicCoverCertificate)
  | strictSignSplit (guard : SymbolicQuadratic)
      (positiveTargets negativeTargets : List (List SymbolicFacet))
      (positiveCover : StrictGuardedSymbolicCoverCertificate)
      (negativeCover : GuardedSymbolicCoverCertificate)
  | split (mid : ℚ)
      (left right : SymbolicIntervalCoverCertificate)

def SymbolicIntervalCoverCertificate.allTargets :
    SymbolicIntervalCoverCertificate → List (List SymbolicFacet)
  | .leaf targets _ => targets
  | .signSplit _ positiveTargets negativeTargets _ _ =>
      positiveTargets ++ negativeTargets
  | .strictSignSplit _ positiveTargets negativeTargets _ _ =>
      positiveTargets ++ negativeTargets
  | .split _ left right => left.allTargets ++ right.allTargets

def SymbolicIntervalCoverCertificate.leafCount :
    SymbolicIntervalCoverCertificate → ℕ
  | .leaf _ _ => 1
  | .signSplit _ _ _ _ _ => 2
  | .strictSignSplit _ _ _ _ _ => 2
  | .split _ left right => left.leafCount + right.leafCount

def SymbolicIntervalCoverCertificate.Check (source : List SymbolicFacet)
    (l u : ℚ) : SymbolicIntervalCoverCertificate → Prop
  | .leaf targets cover => cover.Check source targets l u
  | .signSplit guard positiveTargets negativeTargets positiveCover negativeCover =>
      positiveCover.Check source positiveTargets guard l u ∧
        negativeCover.Check source negativeTargets guard.neg l u
  | .strictSignSplit guard positiveTargets negativeTargets positiveCover negativeCover =>
      positiveCover.Check source positiveTargets guard l u ∧
        negativeCover.Check source negativeTargets guard.neg l u
  | .split mid left right =>
      l < mid ∧ mid < u ∧
        left.Check source l mid ∧ right.Check source mid u

instance symbolicIntervalCoverCheckDecidable (source : List SymbolicFacet)
    (l u : ℚ) (cert : SymbolicIntervalCoverCertificate) :
    Decidable (cert.Check source l u) := by
  induction cert generalizing l u with
  | leaf targets cover =>
      change Decidable (cover.Check source targets l u)
      infer_instance
  | signSplit guard positiveTargets negativeTargets positiveCover negativeCover =>
      change Decidable (positiveCover.Check source positiveTargets guard l u ∧
        negativeCover.Check source negativeTargets guard.neg l u)
      infer_instance
  | strictSignSplit guard positiveTargets negativeTargets positiveCover negativeCover =>
      change Decidable (positiveCover.Check source positiveTargets guard l u ∧
        negativeCover.Check source negativeTargets guard.neg l u)
      infer_instance
  | split mid left right ihl ihr =>
      letI := ihl l mid
      letI := ihr mid u
      change Decidable (l < mid ∧ mid < u ∧
        left.Check source l mid ∧ right.Check source mid u)
      infer_instance

/-- Exact closed interval aggregation, including every rational split point.
The result records which leaf target contains the center, enabling separate
strict capture or blocker proofs for that target. -/
theorem symbolic_interval_cover_sound (source : List SymbolicFacet)
    (l u : ℚ) (cert : SymbolicIntervalCoverCertificate)
    (hc : cert.Check source l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (x : Point) (hx : SymbolicPolygonContains source t x) :
    ∃ target ∈ cert.allTargets, SymbolicPolygonContains target t x := by
  induction cert generalizing l u with
  | leaf targets cover =>
      exact symbolic_cover_sound source targets l u cover hc t hlt htu x hx
  | signSplit guard positiveTargets negativeTargets positiveCover negativeCover =>
      by_cases hguard : 0 ≤ guard.eval t
      · obtain ⟨target, hmem, hcontains⟩ :=
          guarded_symbolic_cover_sound source positiveTargets guard l u
            positiveCover hc.1 t hlt htu hguard x hx
        exact ⟨target, List.mem_append.mpr (Or.inl hmem), hcontains⟩
      · have hneg : 0 ≤ guard.neg.eval t := by
          rw [symbolic_quadratic_neg_eval]
          exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hguard))
        obtain ⟨target, hmem, hcontains⟩ :=
          guarded_symbolic_cover_sound source negativeTargets guard.neg l u
            negativeCover hc.2 t hlt htu hneg x hx
        exact ⟨target, List.mem_append.mpr (Or.inr hmem), hcontains⟩
  | strictSignSplit guard positiveTargets negativeTargets positiveCover negativeCover =>
      by_cases hguard : 0 < guard.eval t
      · obtain ⟨target, hmem, hcontains⟩ :=
          strict_guarded_symbolic_cover_sound source positiveTargets guard l u
            positiveCover hc.1 t hlt htu hguard x hx
        exact ⟨target, List.mem_append.mpr (Or.inl hmem), hcontains⟩
      · have hneg : 0 ≤ guard.neg.eval t := by
          rw [symbolic_quadratic_neg_eval]
          exact neg_nonneg.mpr (le_of_not_gt hguard)
        obtain ⟨target, hmem, hcontains⟩ :=
          guarded_symbolic_cover_sound source negativeTargets guard.neg l u
            negativeCover hc.2 t hlt htu hneg x hx
        exact ⟨target, List.mem_append.mpr (Or.inr hmem), hcontains⟩
  | split mid left right ihl ihr =>
      rcases hc with ⟨_, _, hleft, hright⟩
      by_cases hmid : t ≤ (mid:ℝ)
      · obtain ⟨target, hmem, hcontains⟩ :=
          ihl l mid hleft hlt hmid
        exact ⟨target, List.mem_append.mpr (Or.inl hmem), hcontains⟩
      · have hmid' : (mid:ℝ) ≤ t := le_of_lt (lt_of_not_ge hmid)
        obtain ⟨target, hmem, hcontains⟩ :=
          ihr mid u hright hmid' htu
        exact ⟨target, List.mem_append.mpr (Or.inr hmem), hcontains⟩

theorem symbolic_wall_interval_cover_for_square (q : UnitSquare)
    (cell : Fin 16) (t : ℝ) (l u : ℚ)
    (cert : SymbolicIntervalCoverCertificate)
    (hc : cert.Check (symbolicWallScaledSlab cell) l u)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell cell (normalizeCenter q.center)) :
    ∃ target ∈ cert.allTargets,
      SymbolicPolygonContains target t q.center := by
  exact symbolic_interval_cover_sound (symbolicWallScaledSlab cell) l u
    cert hc t hlt htu q.center
    (symbolic_wall_scaled_slab_contains q cell t ha hcont hcell)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_interval_cover_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_wall_interval_cover_for_square
