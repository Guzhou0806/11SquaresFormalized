import ElevenSquare.Tasks.T07.TightCover
import ElevenSquare.Tasks.T07.ShortcutSiteReduction
import ElevenSquare.Pending.S05_OwnedHull

/-! Five rational points near every occupied covering site. The tighter
Voronoi radius leaves a strict margin for the four `1/200` offsets. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def siteDiamondOffsets : List QPoint :=
  [(0,0), (1/200,0), (-1/200,0), (0,1/200), (0,-1/200)]

def physicalSiteDiamond (i : Fin 16) : List QPoint :=
  siteDiamondOffsets.map fun d =>
    ((physicalSite i).1+d.1, (physicalSite i).2+d.2)

theorem diamond_offset_norm {d : QPoint} (hd : d ∈ siteDiamondOffsets) :
    normSq (realPoint d) ≤ (1/200 : ℝ)^2 := by
  simp only [siteDiamondOffsets, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [normSq, dot, realPoint]

theorem normSq_add_weighted (a b : Point) :
    normSq (a+b) ≤ (101/100 : ℝ)*normSq a + 101*normSq b := by
  dsimp [normSq, dot]
  nlinarith [sq_nonneg (a.1/10-10*b.1), sq_nonneg (a.2/10-10*b.2)]

theorem physicalSiteDiamond_owned_of_closedCell (i : Fin 16) (q : UnitSquare)
    (hcell : ClosedCell i (normalizeCenter q.center))
    {v : QPoint} (hv : v ∈ physicalSiteDiamond i) :
    OpenSquare q (realPoint v) := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
  let s := realPoint (physicalSite i)
  let v : Point := ((physicalSite i).1+d.1, (physicalSite i).2+d.2)
  have hshift : v-s = realPoint d := by
    apply Prod.ext <;> dsimp [v, s, realPoint] <;> ring
  have hbase : normSq (s-q.center) ≤
      (coverCap-1)^2*(17/100 : ℝ)^2 := by
    have hr := closedCell_radius_tight hcell
    have hsym : coordinateDistanceSq (coverSite i) (normalizeCenter q.center) =
        coordinateDistanceSq (normalizeCenter q.center) (coverSite i) := by
      dsimp [coordinateDistanceSq]; ring
    rw [normSq_sub_eq_distance, normalized_distance, normalized_physicalSite, hsym]
    exact mul_le_mul_of_nonneg_left hr (sq_nonneg _)
  have hoff : normSq (v-s) ≤ (1/200 : ℝ)^2 := by
    rw [hshift]
    exact diamond_offset_norm hd
  have hnum : (101/100 : ℝ)*((coverCap-1)^2*(17/100 : ℝ)^2) +
      101*(1/200 : ℝ)^2 < 1/4 := by norm_num [coverCap]
  have hsum : v-q.center = (s-q.center)+(v-s) := by
    apply Prod.ext <;> dsimp [v, s] <;> ring
  have hvEq : realPoint ((physicalSite i).1+d.1, (physicalSite i).2+d.2) = v := by
    apply Prod.ext <;> dsimp [v, realPoint] <;> push_cast <;> ring
  apply open_of_normSq_lt
  rw [hvEq]
  change normSq (v-q.center) < 1/4
  rw [hsum]
  have hw := normSq_add_weighted (s-q.center) (v-s)
  nlinarith only [hw, hbase, hoff, hnum]

def diamondSeed : PoseState where
  rows i := [{ lo := 0, hi := 1, centers := seedCellPolygon (ownerCell i) }]
  owned i := physicalSiteDiamond (ownerCell i)

theorem diamondSeed_holds {S : ℝ} (P : Packing 11 S)
    (hchart : IsCharted P)
    (hcell : ∀ i, ClosedCell (ownerCell i)
      (normalizeCenter (P.squares i).center)) :
    StateHolds P diamondSeed := by
  have hsite := siteSeed_holds P hchart hcell
  constructor
  · exact hsite.1
  · intro i
    apply hull_owned_of_vertices
    intro v hv
    exact physicalSiteDiamond_owned_of_closedCell _ _ (hcell i) hv

end
end ElevenSquare.Tasks.T07
