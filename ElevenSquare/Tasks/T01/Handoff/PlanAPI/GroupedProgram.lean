import ElevenSquare.Tasks.T01.Handoff.PlanAPI.GroupedUniversal

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- A compact row transition. The exact closed cover may use retained center
polygons, direct owned-hull exclusions, ordinary universal pieces, and grouped
universal pieces. Grouped pieces share one strict kernel over several partner
pose rows while still matching the complete predecessor row family. -/
structure GroupedRowPruningCertificate where
  kept : List Polygon
  direct : List ForbiddenPiece
  universal : List UniversalPiece
  grouped : List GroupedUniversalPiece
  cover : BaselineCoverCertificate

def GroupedRowPruningCertificate.targets (c : GroupedRowPruningCertificate) :
    List Polygon :=
  c.kept ++ c.direct.map ForbiddenPiece.polygon ++
    c.universal.map UniversalPiece.polygon ++
    c.grouped.map GroupedUniversalPiece.polygon

def GroupedRowPruningCertificate.Check (s : PoseState) (i : Owner)
    (r : PoseRow) (c : GroupedRowPruningCertificate) : Prop :=
  c.cover.Check r.centers c.targets ∧
  c.direct.Forall (fun p => p.Check s i r) ∧
  c.universal.Forall (fun p => p.Check s i r) ∧
  c.grouped.Forall (fun p => p.Check s i r)

instance groupedRowPruningCertificateCheckDecidable
    (s : PoseState) (i : Owner) (r : PoseRow)
    (c : GroupedRowPruningCertificate) : Decidable (c.Check s i r) := by
  classical
  unfold GroupedRowPruningCertificate.Check
  infer_instance

def GroupedRowPruningCertificate.keptRows (r : PoseRow)
    (c : GroupedRowPruningCertificate) : List PoseRow :=
  c.kept.map (fun polygon => {r with centers := polygon})

theorem grouped_row_pruning_keeps {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (i : Owner) (r : PoseRow)
    (c : GroupedRowPruningCertificate) (hc : c.Check s i r)
    (hs : StateHolds P s) (hq : r.contains (P.squares i)) :
    RowsContain (c.keptRows r) (P.squares i) := by
  obtain ⟨polygon, hpoly, hcenter⟩ := baseline_cover_certificate_sound
    r.centers c.targets c.cover hc.1 (P.squares i).center hq.1
  rcases List.mem_append.mp hpoly with hleft | hgrouped
  · rcases List.mem_append.mp hleft with hleft | huniversal
    · rcases List.mem_append.mp hleft with hkept | hdirect
      · exact ⟨{r with centers := polygon},
          List.mem_map.mpr ⟨polygon, hkept, rfl⟩, hcenter, hq.2⟩
      · obtain ⟨piece, hmem, rfl⟩ := List.mem_map.mp hdirect
        have hp : piece.Check s i r :=
          (List.forall_iff_forall_mem).mp hc.2.1 piece hmem
        have hcore : CoreFits (rationalHull piece.core) (P.squares i) :=
          baseline_row_core_checked r piece.core hp.2.2.2 (P.squares i) hq
        have hbad : (P.squares i).center ∈
            forbiddenCenters (rationalHull (s.owned piece.partner))
              (rationalHull piece.core) :=
          checked_forbidden_polygon (s.owned piece.partner) piece.core
            piece.vertices piece.polygon piece.witnesses hp.2.1 hp.2.2.1 hcenter
        obtain ⟨point, hi, hj⟩ := forbidden_center_implies_overlap
          (P.squares i) (P.squares piece.partner)
          (rationalHull (s.owned piece.partner)) (rationalHull piece.core)
          (hs.2 piece.partner) hcore hbad
        exact False.elim (P.interior_disjoint i piece.partner hp.1 point ⟨hi, hj⟩)
    · obtain ⟨piece, hmem, rfl⟩ := List.mem_map.mp huniversal
      have hp : piece.Check s i r :=
        (List.forall_iff_forall_mem).mp hc.2.2.1 piece hmem
      obtain ⟨point, hi, hj⟩ := universal_piece_collision s i r piece hp
        (P.squares i) (P.squares piece.partner) hq (hs.1 piece.partner) hcenter
      exact False.elim (P.interior_disjoint i piece.partner hp.1 point ⟨hi, hj⟩)
  · obtain ⟨piece, hmem, rfl⟩ := List.mem_map.mp hgrouped
    have hp : piece.Check s i r :=
      (List.forall_iff_forall_mem).mp hc.2.2.2 piece hmem
    obtain ⟨point, hi, hj⟩ := grouped_universal_piece_collision s i r piece hp
      (P.squares i) (P.squares piece.partner) hq (hs.1 piece.partner) hcenter
    exact False.elim (P.interior_disjoint i piece.partner hp.1 point ⟨hi, hj⟩)

def groupedProgramOutput
    (program : List (PoseRow × GroupedRowPruningCertificate)) : List PoseRow :=
  program.bind (fun item => item.2.keptRows item.1)

def GroupedProgramCheck (s : PoseState) (i : Owner)
    (program : List (PoseRow × GroupedRowPruningCertificate)) : Prop :=
  program.map Prod.fst = s.rows i ∧
  program.Forall (fun item => item.2.Check s i item.1)

instance groupedProgramCheckDecidable
    (s : PoseState) (i : Owner)
    (program : List (PoseRow × GroupedRowPruningCertificate)) :
    Decidable (GroupedProgramCheck s i program) := by
  classical
  unfold GroupedProgramCheck
  infer_instance

theorem grouped_program_sound {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (i : Owner)
    (program : List (PoseRow × GroupedRowPruningCertificate))
    (hc : GroupedProgramCheck s i program) (hs : StateHolds P s) :
    StateHolds P (replaceRows s i (groupedProgramOutput program)) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases hj : j = i
  · subst j
    obtain ⟨r, hr, hcontains⟩ := hs.1 i
    rw [← hc.1] at hr
    obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
    have hcheck := (List.forall_iff_forall_mem).mp hc.2 item hm
    obtain ⟨out, hout, hq⟩ :=
      grouped_row_pruning_keeps P s i item.1 item.2 hcheck hs hcontains
    simpa only [replaceRows, Function.update_same] using
      (show RowsContain (groupedProgramOutput program) (P.squares i) from
        ⟨out, List.mem_bind.mpr ⟨item, hm, hout⟩, hq⟩)
  · simpa only [replaceRows, Function.update_noteq hj] using hs.1 j

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.grouped_program_sound
