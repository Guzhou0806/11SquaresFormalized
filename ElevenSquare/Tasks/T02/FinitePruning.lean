import ElevenSquare.Tasks.T02.ConvexWitnesses
import ElevenSquare.Tasks.T02.Quadratic
import ElevenSquare.Pending.S06_BaselineCoverCertificate

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

structure ForbiddenPiece where
  partner : Owner
  core : List QPoint
  vertices : List QPoint
  polygon : Polygon
  witnesses : List DifferenceWitness

def ForbiddenPiece.Check (s : PoseState) (i : Owner) (r : PoseRow)
    (piece : ForbiddenPiece) : Prop :=
  i ≠ piece.partner ∧
  BaselinePolygonCheck piece.vertices piece.polygon ∧
  DifferenceVerticesCheck (s.owned piece.partner) piece.core piece.vertices piece.witnesses ∧
  ∀ v ∈ piece.core, BaselineCoreVertexCheck v r.lo r.hi

instance (s : PoseState) (i : Owner) (r : PoseRow) (piece : ForbiddenPiece) :
    Decidable (piece.Check s i r) := by
  unfold ForbiddenPiece.Check
  infer_instance

structure RowPruningCertificate where
  kept : List Polygon
  forbidden : List ForbiddenPiece
  cover : BaselineCoverCertificate

def RowPruningCertificate.targets (c : RowPruningCertificate) : List Polygon :=
  c.kept ++ c.forbidden.map ForbiddenPiece.polygon

def RowPruningCertificate.Check (s : PoseState) (i : Owner) (r : PoseRow)
    (c : RowPruningCertificate) : Prop :=
  c.cover.Check r.centers c.targets ∧ ∀ p ∈ c.forbidden, p.Check s i r

instance (s : PoseState) (i : Owner) (r : PoseRow) (c : RowPruningCertificate) :
    Decidable (c.Check s i r) := by
  unfold RowPruningCertificate.Check
  infer_instance

def RowPruningCertificate.keptRows (r : PoseRow) (c : RowPruningCertificate) :
    List PoseRow := c.kept.map (fun p => {r with centers := p})

/-- Coverage, forbidden geometry, distinct partner and strict interval core are
all checked separately from the producer's numerical success record. -/
theorem row_pruning_sound (s : PoseState) (i : Owner) (r : PoseRow)
    (c : RowPruningCertificate) (hc : c.Check s i r)
    (q : UnitSquare) (hq : r.contains q) :
    RowsContain (c.keptRows r) q ∨
      ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
        CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q := by
  obtain ⟨poly, hpoly, hp⟩ := baseline_cover_certificate_sound
    r.centers c.targets c.cover hc.1 q.center hq.1
  rcases List.mem_append.mp hpoly with hkeep | hforbid
  · left
    refine ⟨{r with centers := poly}, List.mem_map.mpr ⟨poly, hkeep, rfl⟩, hp, hq.2⟩
  · right
    obtain ⟨piece, hm, rfl⟩ := List.mem_map.mp hforbid
    have h := hc.2 piece hm
    refine ⟨piece.partner, h.1, rationalHull piece.core, ?_, ?_⟩
    · exact baseline_row_core_checked r piece.core h.2.2.2 q hq
    · exact checked_forbidden_polygon (s.owned piece.partner) piece.core
        piece.vertices piece.polygon piece.witnesses h.2.1 h.2.2.1 hp

/-- A plan names its actual predecessor rows. Its output rows are computed,
so a receipt cannot silently substitute a different residual state. -/
def pruningOutput (plan : List (PoseRow × RowPruningCertificate)) : List PoseRow :=
  plan.flatMap (fun item => item.2.keptRows item.1)

theorem checked_pruning_step (s : PoseState) (i : Owner)
    (plan : List (PoseRow × RowPruningCertificate))
    (hinput : plan.map Prod.fst = s.rows i)
    (hcheck : ∀ item ∈ plan, item.2.Check s i item.1) :
    VerifiedStep s (replaceRows s i (pruningOutput plan)) := by
  apply VerifiedStep.prunePosewise
  intro q hq
  rcases hq with ⟨r, hr, hrow⟩
  rw [← hinput] at hr
  obtain ⟨item, hm, heq⟩ := List.mem_map.mp hr
  subst r
  rcases row_pruning_sound s i item.1 item.2 (hcheck item hm) q hrow with hk | hb
  · left
    rcases hk with ⟨out, ho, hcontains⟩
    exact ⟨out, List.mem_flatMap.mpr ⟨item, hm, ho⟩, hcontains⟩
  · exact Or.inr hb

end
end ElevenSquare.Tasks.T02
