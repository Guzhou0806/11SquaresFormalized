import ElevenSquare.Tasks.T01.DirectOwnership

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- One retained-center inequality implying that a fresh point's offset
    satisfies a facet of a common strict core. -/
structure RetainedCoreFacetWitness where
  facet : Halfplane
  bound : ℚ
  combination : BaselineCombination

def RetainedCoreFacetWitness.translatedCut
    (w : RetainedCoreFacetWitness) : Halfplane :=
  ⟨-w.facet.a, -w.facet.b, w.bound⟩

def coreFreshRhs (facet : Halfplane) (p : QPoint) : ℚ :=
  facet.c - facet.a * p.1 - facet.b * p.2

/-- The strongest common translated cut for a nonempty fresh-point list. -/
def minCoreBound : List QPoint → Halfplane → ℚ
  | [], _ => 0
  | p :: ps, facet =>
      (ps.map (coreFreshRhs facet)).foldl min (coreFreshRhs facet p)

private theorem foldl_min_le_init (xs : List ℚ) (init : ℚ) :
    xs.foldl min init ≤ init := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simpa only [List.foldl_cons] using
        (ih (min init x)).trans (min_le_left init x)

private theorem foldl_min_le_mem (xs : List ℚ) (init q : ℚ)
    (hq : q ∈ xs) : xs.foldl min init ≤ q := by
  induction xs generalizing init with
  | nil => simp at hq
  | cons x xs ih =>
      rcases List.mem_cons.mp hq with rfl | hq
      · simpa only [List.foldl_cons] using
          (foldl_min_le_init xs (min init q)).trans (min_le_right init q)
      · simpa only [List.foldl_cons] using ih (min init x) hq

theorem minCoreBound_le (fresh : List QPoint) (facet : Halfplane)
    (p : QPoint) (hp : p ∈ fresh) :
    minCoreBound fresh facet ≤ coreFreshRhs facet p := by
  cases fresh with
  | nil => simp at hp
  | cons p0 ps =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact foldl_min_le_init _ _
      · exact foldl_min_le_mem _ _ _
          (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- The polygon for retained centers implies one translated inequality per
    core facet. The bound comparison is linear in each fresh point. -/
def RetainedCoreFreshCheck (row : PoseRow) (coreVertices : List QPoint)
    (corePolygon : Polygon) (fresh : List QPoint)
    (witnesses : List RetainedCoreFacetWitness) : Prop :=
  BaselinePolygonCheck coreVertices corePolygon ∧
  (∀ v ∈ coreVertices, BaselineCoreVertexCheck v row.lo row.hi) ∧
  witnesses.map (·.facet) = corePolygon ∧
  ∀ w ∈ witnesses,
    BaselineImplicationCheck row.centers w.translatedCut w.combination ∧
    ∀ p ∈ fresh,
      w.bound ≤ w.facet.c - w.facet.a * p.1 - w.facet.b * p.2

instance (row : PoseRow) (coreVertices : List QPoint)
    (corePolygon : Polygon) (fresh : List QPoint)
    (witnesses : List RetainedCoreFacetWitness) :
    Decidable (RetainedCoreFreshCheck row coreVertices corePolygon fresh witnesses) := by
  unfold RetainedCoreFreshCheck
  infer_instance

/-- A retained center and a core-facet certificate place every fresh point
    strictly inside the square. This replaces per-point, per-center-vertex
    quadratic checks by one core check and translated facet implications. -/
theorem retained_core_fresh_sound (row : PoseRow)
    (coreVertices : List QPoint) (corePolygon : Polygon)
    (fresh : List QPoint) (witnesses : List RetainedCoreFacetWitness)
    (hcheck : RetainedCoreFreshCheck row coreVertices corePolygon fresh witnesses)
    (q : UnitSquare) (hq : row.contains q) (p : QPoint) (hp : p ∈ fresh) :
    OpenSquare q (realPoint p) := by
  have hcore : CoreFits (rationalHull coreVertices) q :=
    baseline_row_core_checked row coreVertices hcheck.2.1 q hq
  have hoffset : realPoint p - q.center ∈ corePolygon.carrier := by
    intro f hf
    rw [← hcheck.2.2.1] at hf
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hf
    have hwcheck := hcheck.2.2.2 w hw
    have hcut := baseline_implication_check_sound row.centers w.translatedCut
      w.combination hwcheck.1 q.center hq.1
    have hbound : (w.bound : ℝ) ≤
        (w.facet.c : ℝ) - (w.facet.a : ℝ) * (p.1 : ℝ) -
          (w.facet.b : ℝ) * (p.2 : ℝ) := by
      exact_mod_cast hwcheck.2 p hp
    dsimp [Halfplane.contains, RetainedCoreFacetWitness.translatedCut,
      realPoint] at hcut ⊢
    push_cast at hcut
    linarith
  have hhull := baseline_polygon_check_sound coreVertices corePolygon
    hcheck.1 hoffset
  have hopen := hcore (realPoint p - q.center) hhull
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hopen

/-- Promote a common finite fresh-point set after every live row has a
    retained-core certificate. -/
theorem checked_retained_core_promotion (s : PoseState) (i : Owner)
    (fresh : List QPoint) (coreVertices : PoseRow → List QPoint)
    (corePolygon : PoseRow → Polygon)
    (witnesses : PoseRow → List RetainedCoreFacetWitness)
    (hcheck : ∀ row ∈ s.rows i,
      RetainedCoreFreshCheck row (coreVertices row) (corePolygon row)
        fresh (witnesses row)) :
    VerifiedStep s (replaceHull s i (s.owned i ++ fresh)) := by
  apply VerifiedStep.promoteOwned
  intro q hq hold p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hold (subset_convexHull ℝ _ ⟨p, hp, rfl⟩)
  · obtain ⟨row, hr, hrow⟩ := hq
    exact retained_core_fresh_sound row (coreVertices row)
      (corePolygon row) fresh (witnesses row) (hcheck row hr) q hrow p hp

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.retained_core_fresh_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.checked_retained_core_promotion
