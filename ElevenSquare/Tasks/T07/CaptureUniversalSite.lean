import ElevenSquare.Tasks.T07.CaptureSeedGeometry
import ElevenSquare.Pending.S05_OwnedHull
import Mathlib.Tactic.NormNum

/-! A short initial ownership certificate. Every center in a closed cover cell
is within less than one half of its site's physical position. This gives an
angle-independent owned point without replaying any pose rows. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def seedPhysicalSiteQ (i : Fin 16) : QPoint :=
  (1/2+(seedCap-1)*(seedSite i).1,
    1/2+(seedCap-1)*(seedSite i).2)

theorem seedPhysicalSiteQ_normalized (i : Fin 16) :
    normalizeCenter (realPoint (seedPhysicalSiteQ i)) = coverSite i := by
  rw [← seedSite_cast i]
  have hne : coverCap-1 ≠ 0 := ne_of_gt (sub_pos.mpr coverCap_gt_one)
  apply Prod.ext
  · dsimp [normalizeCenter, realPoint, seedPhysicalSiteQ]
    rw [← seedCap_cast]
    push_cast
    field_simp [show (seedCap : ℝ)-1 ≠ 0 by rw [seedCap_cast]; exact hne] <;> ring
  · dsimp [normalizeCenter, realPoint, seedPhysicalSiteQ]
    rw [← seedCap_cast]
    push_cast
    field_simp [show (seedCap : ℝ)-1 ≠ 0 by rw [seedCap_cast]; exact hne] <;> ring

theorem seed_cell_site_owned (q : UnitSquare) (i : Fin 16)
    (hcell : ClosedCell i (normalizeCenter q.center)) :
    OpenSquare q (realPoint (seedPhysicalSiteQ i)) := by
  let w := realPoint (seedPhysicalSiteQ i)
  have hcomm : coordinateDistanceSq w q.center =
      coordinateDistanceSq q.center w := by
    dsimp [coordinateDistanceSq]
    ring
  have hdist : normSq (w-q.center) =
      (coverCap-1)^2 *
        coordinateDistanceSq (normalizeCenter q.center) (coverSite i) := by
    rw [normSq_sub_eq_distance, hcomm, normalized_distance]
    exact congrArg
      (fun z : Point => (coverCap-1)^2 *
        coordinateDistanceSq (normalizeCenter q.center) z)
      (seedPhysicalSiteQ_normalized i)
  have hrad := closedCell_radius hcell
  have hmul := mul_le_mul_of_nonneg_left hrad (sq_nonneg (coverCap-1))
  have hstrict : (coverCap-1)^2 * coverRadius^2 < 1/4 := by
    norm_num [coverCap, coverRadius]
  apply owned_vertex_of_disk q w
  rw [hdist]
  exact lt_of_le_of_lt hmul hstrict

end
end ElevenSquare.Tasks.T07
