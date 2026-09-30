import ElevenSquare.Tasks.T07.LocalTraceCover
import ElevenSquare.Tasks.T07.CaptureCuts
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

/-! One sound checker interface for routine phase-2 row propagation. A source
row is split into closed polygon regions; each region must either reach a
retained pose row or carry a genuine collision witness. Rows absent from the
prior active cover do not appear in this obligation. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem routine_row_from_regions (s : PoseState) (i : Owner)
    (rs : List PoseRow) (r : PoseRow) (regions : List Polygon)
    (hpoly : PolygonCoverCert regions r.centers)
    (hregion : ∀ K ∈ regions, ∀ q : UnitSquare, r.contains q →
      q.center ∈ K.carrier →
      RowsContain rs q ∨
        ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
          CoreFits Q q ∧
          q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q)
    (q : UnitSquare) (hr : r.contains q) :
    RowsContain rs q ∨
      ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
        CoreFits Q q ∧
        q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q := by
  have hu := hpoly.sound hr.1
  obtain ⟨K, hK⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hKmem, hKcenter⟩ := Set.mem_iUnion.mp hK
  exact hregion K hKmem q hr hKcenter

/-- A generator supplies one finite polygon-cover certificate per *active*
old row. The two generic lines below assemble them into an S05 VerifiedStep.
Prior-angle-excluded archive slots have no active old row and need no branch. -/
theorem verifiedStep_of_routine_regions (s : PoseState) (i : Owner)
    (rs : List PoseRow) (regions : PoseRow → List Polygon)
    (hpoly : ∀ r ∈ s.rows i,
      PolygonCoverCert (regions r) r.centers)
    (hregion : ∀ r ∈ s.rows i, ∀ K ∈ regions r,
      ∀ q : UnitSquare, r.contains q → q.center ∈ K.carrier →
      RowsContain rs q ∨
        ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
          CoreFits Q q ∧
          q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q) :
    VerifiedStep s (replaceRows s i rs) := by
  apply prunePosewise_of_row_certificates
  intro r hr q hq
  exact routine_row_from_regions s i rs r (regions r)
    (hpoly r hr) (hregion r hr) q hq

/-- A particular row can be skipped when the already fixed chart parameter
lies strictly above its entire closed angular interval. -/
theorem row_excluded_by_angle_upper (r : PoseRow) (q : UnitSquare)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (ha : q.axis = chartAxis t₀) (hhi : (r.hi : ℝ) < t₀) :
    ¬ r.contains q := by
  rintro ⟨_, t, ht, ht1, _, hrowhi, htaxis⟩
  have heq := chartAxis_injective_of_nonneg ht ht₀ (htaxis.symm.trans ha)
  rw [heq] at hrowhi
  exact (not_lt_of_ge hrowhi) hhi

/-- The symmetric exclusion when the fixed chart parameter lies below the
entire closed interval. Endpoints are retained because both comparisons are
strict. -/
theorem row_excluded_by_angle_lower (r : PoseRow) (q : UnitSquare)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (ha : q.axis = chartAxis t₀) (hlo : t₀ < (r.lo : ℝ)) :
    ¬ r.contains q := by
  rintro ⟨_, t, ht, ht1, hrowlo, _, htaxis⟩
  have heq := chartAxis_injective_of_nonneg ht ht₀ (htaxis.symm.trans ha)
  rw [heq] at hrowlo
  exact (not_lt_of_ge hrowlo) hlo

end
end ElevenSquare.Tasks.T07
