import ElevenSquare.Pending.S05_Trace
import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- A small exact witness for membership in a rational convex hull. -/
inductive HullWitness where
  | vertex (index : ℕ)
  | mix (weight : ℚ) (left right : HullWitness)
  deriving Repr

def rationalMix (w : ℚ) (a b : QPoint) : QPoint :=
  ((1-w)*a.1+w*b.1, (1-w)*a.2+w*b.2)

def HullWitness.eval (vs : List QPoint) : HullWitness → QPoint
  | .vertex i => vs.getD i (0,0)
  | .mix w a b => rationalMix w (a.eval vs) (b.eval vs)

def HullWitness.Valid (vs : List QPoint) : HullWitness → Prop
  | .vertex i => i < vs.length
  | .mix w a b => 0 ≤ w ∧ w ≤ 1 ∧ a.Valid vs ∧ b.Valid vs

instance (vs : List QPoint) (w : HullWitness) : Decidable (w.Valid vs) := by
  induction w with
  | vertex i => exact inferInstanceAs (Decidable (i < vs.length))
  | mix w a b ia ib =>
    letI := ia
    letI := ib
    exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem realPoint_rationalMix (w : ℚ) (a b : QPoint) :
    realPoint (rationalMix w a b) =
      (1 - (w : ℝ)) • realPoint a + (w : ℝ) • realPoint b := by
  ext <;> simp [rationalMix, realPoint]

theorem hullWitness_sound (vs : List QPoint) (w : HullWitness) (hw : w.Valid vs) :
    realPoint (w.eval vs) ∈ rationalHull vs := by
  induction w with
  | vertex i =>
    apply subset_convexHull ℝ _
    refine ⟨vs.getD i (0,0), ?_, rfl⟩
    rw [List.getD_eq_getElem vs (0,0) hw]
    exact List.get_mem ..
  | mix w a b ia ib =>
    change realPoint (rationalMix w (a.eval vs) (b.eval vs)) ∈ rationalHull vs
    rw [realPoint_rationalMix]
    exact (convex_convexHull ℝ _) (ia hw.2.2.1) (ib hw.2.2.2)
      (sub_nonneg.mpr (by exact_mod_cast hw.2.1))
      (by exact_mod_cast hw.1) (sub_add_cancel 1 (w : ℝ))

/-- Closed Minkowski difference of two convex sets is convex. Its later overlap
consequence remains strict because both input hulls fit in open squares. -/
theorem forbiddenCenters_convex (K Q : Set Point) (hK : Convex ℝ K)
    (hQ : Convex ℝ Q) : Convex ℝ (forbiddenCenters K Q) := by
  rintro x ⟨k, hk, v, hv, rfl⟩ y ⟨l, hl, w, hw, rfl⟩ a b ha hb hab
  refine ⟨a • k + b • l, hK hk hl ha hb hab,
    a • v + b • w, hQ hv hw ha hb hab, ?_⟩
  ext <;> simp [smul_sub, sub_add_sub_comm]

structure DifferenceWitness where
  owned : HullWitness
  core : HullWitness

def DifferenceWitness.eval (K Q : List QPoint) (w : DifferenceWitness) : QPoint :=
  let a := w.owned.eval K
  let b := w.core.eval Q
  (a.1-b.1, a.2-b.2)

def DifferenceWitness.Valid (K Q : List QPoint) (w : DifferenceWitness) : Prop :=
  w.owned.Valid K ∧ w.core.Valid Q

instance (K Q : List QPoint) (w : DifferenceWitness) : Decidable (w.Valid K Q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem differenceWitness_sound (K Q : List QPoint) (w : DifferenceWitness)
    (hw : w.Valid K Q) :
    realPoint (w.eval K Q) ∈ forbiddenCenters (rationalHull K) (rationalHull Q) := by
  refine ⟨realPoint (w.owned.eval K), hullWitness_sound K w.owned hw.1,
    realPoint (w.core.eval Q), hullWitness_sound Q w.core hw.2, ?_⟩
  ext <;> simp [DifferenceWitness.eval, realPoint]

/-- Each vertex has an explicit pair of small hull witnesses. -/
def DifferenceVerticesCheck (K Q vs : List QPoint)
    (ws : List DifferenceWitness) : Prop :=
  vs.length = ws.length ∧
  ∀ vw ∈ vs.zip ws, vw.2.Valid K Q ∧ vw.1 = vw.2.eval K Q

instance (K Q vs : List QPoint) (ws : List DifferenceWitness) :
    Decidable (DifferenceVerticesCheck K Q vs ws) := by
  unfold DifferenceVerticesCheck
  infer_instance

theorem difference_vertices_sound (K Q vs : List QPoint) (ws : List DifferenceWitness)
    (hc : DifferenceVerticesCheck K Q vs ws) :
    ∀ v ∈ vs, realPoint v ∈ forbiddenCenters (rationalHull K) (rationalHull Q) := by
  induction vs generalizing ws with
  | nil => simp
  | cons v vs ih =>
    cases ws with
    | nil => simp [DifferenceVerticesCheck] at hc
    | cons w ws =>
      have hw := hc.2 (v,w) (by simp)
      dsimp only [Prod.fst, Prod.snd] at hw
      have ht : DifferenceVerticesCheck K Q vs ws := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro x hx
        exact hc.2 x (by simp [hx])
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [hw.2]
        exact differenceWitness_sound K Q w hw.1
      · exact ih ws ht p hp

/-- A rational halfplane polygon is a forbidden-center region after exact
halfplane-to-hull and vertex-witness checks. -/
theorem checked_forbidden_polygon (K Q vs : List QPoint) (hs : Polygon)
    (ws : List DifferenceWitness) (hpoly : BaselinePolygonCheck vs hs)
    (hvertices : DifferenceVerticesCheck K Q vs ws) :
    hs.carrier ⊆ forbiddenCenters (rationalHull K) (rationalHull Q) := by
  apply (baseline_polygon_check_sound vs hs hpoly).trans
  apply convexHull_min _ (forbiddenCenters_convex _ _
    (convex_convexHull ℝ _) (convex_convexHull ℝ _))
  rintro p ⟨v, hv, rfl⟩
  exact difference_vertices_sound K Q vs ws hvertices v hv

end
end ElevenSquare.Tasks.T01
