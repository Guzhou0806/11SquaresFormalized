import ElevenSquare.Tasks.T01.Handoff.GenericPorter.RealPolygonSound
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.MovingCore
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCover
import ElevenSquare.Tasks.T01.ConvexWitnesses

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

structure MovingDifferenceWitness where
  owned : HullWitness
  localIndex : ℕ

def MovingDifferenceWitness.Valid (K : List QPoint) (locals : List (ℝ × ℝ))
    (w : MovingDifferenceWitness) : Prop :=
  w.owned.Valid K ∧ w.localIndex < locals.length

def MovingDifferenceWitness.eval (K : List QPoint) (locals : List (ℝ × ℝ))
    (q : UnitSquare) (w : MovingDifferenceWitness) : Point :=
  let ab := locals.getD w.localIndex (0,0)
  realPoint (w.owned.eval K) - localOffset q ab.1 ab.2

theorem movingDifferenceWitness_sound (K : List QPoint)
    (locals : List (ℝ × ℝ)) (q : UnitSquare) (w : MovingDifferenceWitness)
    (hw : w.Valid K locals) :
    w.eval K locals q ∈ forbiddenCenters (rationalHull K) (movingCore q locals) := by
  let ab := locals.getD w.localIndex (0,0)
  have hab : ab ∈ locals := by
    dsimp [ab]
    rw [List.getD_eq_get locals (0,0) hw.2]
    exact List.get_mem ..
  refine ⟨realPoint (w.owned.eval K), hullWitness_sound K w.owned hw.1,
    localOffset q ab.1 ab.2, ?_, rfl⟩
  apply subset_convexHull ℝ _
  exact ⟨ab, hab, rfl⟩

def MovingDifferenceVerticesCheck (K : List QPoint)
    (locals : List (ℝ × ℝ)) (q : UnitSquare)
    (vertices : List Point) (ws : List MovingDifferenceWitness) : Prop :=
  vertices.length = ws.length ∧
  ∀ vw ∈ vertices.zip ws, vw.2.Valid K locals ∧ vw.1 = vw.2.eval K locals q

theorem movingDifferenceVertices_sound (K : List QPoint)
    (locals : List (ℝ × ℝ)) (q : UnitSquare)
    (vertices : List Point) (ws : List MovingDifferenceWitness)
    (hc : MovingDifferenceVerticesCheck K locals q vertices ws) :
    ∀ v ∈ vertices,
      v ∈ forbiddenCenters (rationalHull K) (movingCore q locals) := by
  induction vertices generalizing ws with
  | nil => simp
  | cons v tail ih =>
    cases ws with
    | nil => simp [MovingDifferenceVerticesCheck] at hc
    | cons w wtail =>
      have hw := hc.2 (v,w) (by simp)
      dsimp only [Prod.fst, Prod.snd] at hw
      have ht : MovingDifferenceVerticesCheck K locals q tail wtail := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro x hx
        exact hc.2 x (by simp [hx])
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [hw.2]
        exact movingDifferenceWitness_sound K locals q w hw.1
      · exact ih wtail ht p hp

theorem real_moving_forbidden_sound (K : List QPoint)
    (locals : List (ℝ × ℝ)) (q : UnitSquare)
    (vertices : List Point) (hs : List RealHalfplane)
    (ws : List MovingDifferenceWitness)
    (hpoly : RealPolygonCheck vertices hs)
    (hw : MovingDifferenceVerticesCheck K locals q vertices ws) :
    RealPolygon.carrier hs ⊆ forbiddenCenters (rationalHull K) (movingCore q locals) := by
  apply (real_polygon_check_sound vertices hs hpoly).trans
  apply convexHull_min _
    (forbiddenCenters_convex _ _ (convex_convexHull ℝ _) (convex_convexHull ℝ _))
  intro v hv
  exact movingDifferenceVertices_sound K locals q vertices ws hw v hv

theorem real_moving_forbidden_support_sound (K : List QPoint)
    (locals : List (ℝ × ℝ)) (q : UnitSquare)
    (vertices : List Point) (hs : List RealHalfplane)
    (ws : List MovingDifferenceWitness)
    (hpoly : RealPolygonSupportCheck vertices hs)
    (hw : MovingDifferenceVerticesCheck K locals q vertices ws) :
    RealPolygon.carrier hs ⊆ forbiddenCenters (rationalHull K) (movingCore q locals) := by
  apply (real_polygon_support_sound vertices hs hpoly).trans
  apply convexHull_min _
    (forbiddenCenters_convex _ _ (convex_convexHull ℝ _) (convex_convexHull ℝ _))
  intro v hv
  exact movingDifferenceVertices_sound K locals q vertices ws hw v hv

def symbolicFacetReal (f : SymbolicFacet) (t : ℝ) : RealHalfplane :=
  ⟨f.a.eval t, f.b.eval t, f.c.eval t⟩

theorem symbolic_contains_real (hs : List SymbolicFacet) (t : ℝ) (p : Point)
    (hp : SymbolicPolygonContains hs t p) :
    p ∈ RealPolygon.carrier (hs.map (fun f => symbolicFacetReal f t)) := by
  intro h hh
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hh
  exact hp f hf

/-- The moving symbolic target is sound when its complete oriented edge
    list and every pair-difference vertex are certified for this angle. -/
theorem moving_symbolic_forbidden_sound (K : List QPoint)
    (locals : List (ℝ × ℝ)) (q : UnitSquare) (t : ℝ)
    (facets : List SymbolicFacet) (vertices : List Point)
    (ws : List MovingDifferenceWitness)
    (hlocal : ∀ ab ∈ locals, |ab.1| < 1/2 ∧ |ab.2| < 1/2)
    (hpoly : RealPolygonCheck vertices
      (facets.map (fun f => symbolicFacetReal f t)))
    (hw : MovingDifferenceVerticesCheck K locals q vertices ws)
    (hc : SymbolicPolygonContains facets t q.center) :
    ∃ Q : Set Point,
      CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull K) Q := by
  refine ⟨movingCore q locals, movingCore_fits q locals hlocal, ?_⟩
  exact real_moving_forbidden_sound K locals q vertices _ ws hpoly hw
    (symbolic_contains_real facets t q.center hc)

theorem moving_symbolic_forbidden_support_sound (K : List QPoint)
    (locals : List (ℝ × ℝ)) (q : UnitSquare) (t : ℝ)
    (facets : List SymbolicFacet) (vertices : List Point)
    (ws : List MovingDifferenceWitness)
    (hlocal : ∀ ab ∈ locals, |ab.1| < 1/2 ∧ |ab.2| < 1/2)
    (hpoly : RealPolygonSupportCheck vertices
      (facets.map (fun f => symbolicFacetReal f t)))
    (hw : MovingDifferenceVerticesCheck K locals q vertices ws)
    (hc : SymbolicPolygonContains facets t q.center) :
    ∃ Q : Set Point,
      CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull K) Q := by
  refine ⟨movingCore q locals, movingCore_fits q locals hlocal, ?_⟩
  exact real_moving_forbidden_support_sound K locals q vertices _ ws hpoly hw
    (symbolic_contains_real facets t q.center hc)

#print axioms moving_symbolic_forbidden_sound
#print axioms moving_symbolic_forbidden_support_sound

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter
