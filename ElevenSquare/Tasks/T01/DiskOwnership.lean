import ElevenSquare.Tasks.T01.Root
import ElevenSquare.Pending.S05_Trace
import ElevenSquare.Pending.S06_BaselineCoverCertificate

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

def DiskPointCheck (centers : List QPoint) (p : QPoint) : Prop :=
  ∀ c ∈ centers, (p.1-c.1)^2+(p.2-c.2)^2 < 1/4

instance diskPointCheckDecidable (centers : List QPoint) (p : QPoint) :
    Decidable (DiskPointCheck centers p) := by
  unfold DiskPointCheck
  infer_instance

/-- A vertex distance test proves ownership for every orientation. -/
theorem disk_point_owned (centers : List QPoint) (p : QPoint)
    (hc : DiskPointCheck centers p) (q : UnitSquare)
    (hq : q.center ∈ rationalHull centers) : OpenSquare q (realPoint p) := by
  let f : Point →ᵃ[ℝ] Point :=
    AffineMap.const ℝ Point (q.center + realPoint p) - AffineMap.id ℝ Point
  have hconv : Convex ℝ {c : Point | OpenSquare q (q.center + realPoint p - c)} := by
    simpa [f] using (openSquare_convex q).affine_preimage f
  have hv : {c | ∃ v ∈ centers, c = realPoint v} ⊆
      {c | OpenSquare q (q.center + realPoint p - c)} := by
    rintro c ⟨v, hmem, rfl⟩
    apply open_of_normSq_lt
    have hdist : ((p.1 : ℝ)-(v.1 : ℝ))^2+((p.2 : ℝ)-(v.2 : ℝ))^2 < 1/4 := by
      have hr : (p.1-v.1)^2+(p.2-v.2)^2 < (1/4 : ℚ) := hc v hmem
      have hs : (((p.1-v.1)^2+(p.2-v.2)^2 : ℚ) : ℝ) < ((1/4 : ℚ) : ℝ) :=
        Rat.cast_lt.mpr hr
      norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_pow, Rat.cast_div,
        Rat.cast_one, Rat.cast_ofNat] at hs
      exact hs
    dsimp [normSq, dot, realPoint]
    nlinarith [hdist]
  have hp := (convexHull_min hv hconv) hq
  simpa using hp

theorem disk_cell_owned_hull (cell : Fin 16) (centers owned : List QPoint)
    (polygon : Polygon) (witnesses : List BaselineCombination)
    (hcover : BaselinePolygonImplicationCheck (baselineCellPolygon cell) polygon witnesses)
    (hpoly : BaselinePolygonCheck centers polygon)
    (hpoints : ∀ p ∈ owned, DiskPointCheck centers p)
    (q : UnitSquare) (hq : ClosedCell cell (normalizeCenter q.center)) :
    rationalHull owned ⊆ {p | OpenSquare q p} := by
  have hcenter := baseline_polygon_check_sound centers polygon hpoly
    (baseline_polygon_implication_check_sound _ _ _ hcover (baselineCellPolygon_contains hq))
  exact hull_owned_of_vertices q owned (fun p hp => disk_point_owned centers p (hpoints p hp) q hcenter)

end
end ElevenSquare.Tasks.T01
