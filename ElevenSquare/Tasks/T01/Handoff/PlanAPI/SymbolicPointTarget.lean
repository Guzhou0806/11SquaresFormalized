import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab
import ElevenSquare.Tasks.T01.ConvexWitnesses

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Four signed chart directions after clearing `1+t²`. -/
def symbolicPointNormal : Fin 4 → SymbolicQuadratic × SymbolicQuadratic :=
  ![(⟨1,0,-1⟩, ⟨0,2,0⟩), (⟨-1,0,1⟩, ⟨0,-2,0⟩),
    (⟨0,-2,0⟩, ⟨1,0,-1⟩), (⟨0,2,0⟩, ⟨-1,0,1⟩)]

def symbolicPointBound (a b : SymbolicQuadratic) (p : QPoint)
    (h : ℚ) : SymbolicQuadratic :=
  ⟨a.c0*p.1+b.c0*p.2+h,
   a.c1*p.1+b.c1*p.2,
   a.c2*p.1+b.c2*p.2+h⟩

/-- A strict inner-square point-capture facet. Its inequality is closed,
but `h<1/2` turns the resulting point capture into an open-square fact. -/
def symbolicPointFacet (p : QPoint) (h : ℚ) (k : Fin 4) : SymbolicFacet :=
  let n := symbolicPointNormal k
  ⟨n.1, n.2, symbolicPointBound n.1 n.2 p h⟩

def symbolicPointTarget (p : QPoint) (h : ℚ) : List SymbolicFacet :=
  (List.finRange 4).map (symbolicPointFacet p h)

theorem symbolic_point_normal_eval (k : Fin 4) (t : ℝ) :
    ((symbolicPointNormal k).1.eval t,
      (symbolicPointNormal k).2.eval t) = chartDirectionNumerator t k := by
  fin_cases k <;> simp [symbolicPointNormal, SymbolicQuadratic.eval,
    chartDirectionNumerator] <;> ring

theorem symbolic_point_bound_eval (p : QPoint) (h : ℚ)
    (k : Fin 4) (t : ℝ) :
    (symbolicPointFacet p h k).c.eval t =
      dot (chartDirectionNumerator t k) (realPoint p) + h*(1+t^2) := by
  fin_cases k <;>
    simp [symbolicPointFacet, symbolicPointBound, symbolicPointNormal,
      SymbolicQuadratic.eval, chartDirectionNumerator, dot, realPoint] <;>
    ring

/-- Membership in a four-facet symbolic target gives strict capture of the
point for every real chart angle, including angle and region boundaries. -/
theorem symbolic_point_target_sound (q : UnitSquare) (p : QPoint)
    (h : ℚ) (target : List SymbolicFacet) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hwidth : 0 ≤ h ∧ h < 1/2)
    (hfacets : ∀ f ∈ symbolicPointTarget p h, f ∈ target)
    (hcenter : SymbolicPolygonContains target t q.center) :
    OpenSquare q (realPoint p) := by
  apply point_owned_of_direction_numerators q (realPoint p) t ha
  intro k
  have hmem : symbolicPointFacet p h k ∈ symbolicPointTarget p h :=
    List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
  have hfacet := hcenter _ (hfacets _ hmem)
  have hn := symbolic_point_normal_eval k t
  have hna : (symbolicPointNormal k).1.eval t =
      (chartDirectionNumerator t k).1 := by
    simpa using congrArg Prod.fst hn
  have hnb : (symbolicPointNormal k).2.eval t =
      (chartDirectionNumerator t k).2 := by
    simpa using congrArg Prod.snd hn
  unfold SymbolicFacet.contains at hfacet
  change (symbolicPointNormal k).1.eval t * q.center.1 +
      (symbolicPointNormal k).2.eval t * q.center.2 ≤
      (symbolicPointFacet p h k).c.eval t at hfacet
  rw [symbolic_point_bound_eval, hna, hnb] at hfacet
  have hd : 0 < 1+t^2 := by positivity
  have hh : (h:ℝ) < 1/2 := by
    have h' : (h:ℝ) < ((1/2:ℚ):ℝ) := by exact_mod_cast hwidth.2
    norm_num at h' ⊢
    exact h'
  have hstrict : (h:ℝ)*(1+t^2) < (1+t^2)/2 := by
    have hmul := mul_lt_mul_of_pos_right hh hd
    linarith
  have hdot : dot (chartDirectionNumerator t k) (q.center - realPoint p) =
      dot (chartDirectionNumerator t k) q.center -
        dot (chartDirectionNumerator t k) (realPoint p) := by
    simp [dot]
    ring
  rw [hdot]
  dsimp [dot] at hfacet ⊢
  linarith

theorem symbolic_point_block_impossible {S : ℝ} (P : Packing 11 S)
    (i j : Owner) (hij : i ≠ j) (p : QPoint) (h : ℚ)
    (target : List SymbolicFacet) (t : ℝ)
    (ha : (P.squares i).axis = chartAxis t)
    (hwidth : 0 ≤ h ∧ h < 1/2)
    (hfacets : ∀ f ∈ symbolicPointTarget p h, f ∈ target)
    (hcenter : SymbolicPolygonContains target t (P.squares i).center)
    (howned : OpenSquare (P.squares j) (realPoint p)) : False := by
  have hi := symbolic_point_target_sound (P.squares i) p h target t
    ha hwidth hfacets hcenter
  exact P.interior_disjoint i j hij (realPoint p) ⟨hi, howned⟩

/-- A point target also records an already owned witness in another square.
All fields of `Check` are finite rational or list checks. -/
structure SymbolicOwnedBlockTarget where
  polygon : List SymbolicFacet
  point : QPoint
  partner : Owner
  witness : HullWitness
  halfWidth : ℚ

def SymbolicOwnedBlockTarget.Check (s : PoseState) (i : Owner)
    (c : SymbolicOwnedBlockTarget) : Prop :=
  i ≠ c.partner ∧ c.witness.Valid (s.owned c.partner) ∧
    c.witness.eval (s.owned c.partner) = c.point ∧
    0 ≤ c.halfWidth ∧ c.halfWidth < 1/2 ∧
    ∀ f ∈ symbolicPointTarget c.point c.halfWidth,
      f ∈ c.polygon

instance symbolicOwnedBlockTargetCheckDecidable (s : PoseState)
    (i : Owner) (c : SymbolicOwnedBlockTarget) :
    Decidable (c.Check s i) := by
  unfold SymbolicOwnedBlockTarget.Check
  infer_instance

theorem symbolic_owned_block_target_impossible {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) (i : Owner)
    (c : SymbolicOwnedBlockTarget) (hc : c.Check s i)
    (t : ℝ) (ha : (P.squares i).axis = chartAxis t)
    (hcenter : SymbolicPolygonContains c.polygon t (P.squares i).center) :
    False := by
  have hi : OpenSquare (P.squares i) (realPoint c.point) :=
    symbolic_point_target_sound (P.squares i) c.point c.halfWidth
      c.polygon t ha ⟨hc.2.2.2.1, hc.2.2.2.2.1⟩ hc.2.2.2.2.2 hcenter
  have hmember : realPoint c.point ∈
      rationalHull (s.owned c.partner) := by
    rw [← hc.2.2.1]
    exact hullWitness_sound (s.owned c.partner) c.witness hc.2.1
  have hj : OpenSquare (P.squares c.partner)
      (realPoint c.point) := hs.2 c.partner hmember
  exact P.interior_disjoint i c.partner hc.1 (realPoint c.point) ⟨hi, hj⟩

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_point_target_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_point_block_impossible
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_owned_block_target_impossible
