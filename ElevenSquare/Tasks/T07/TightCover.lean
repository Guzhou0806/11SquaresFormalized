import ElevenSquare.Tasks.T07.TightCover0
import ElevenSquare.Tasks.T07.TightCover1
import ElevenSquare.Tasks.T07.TightCover2
import ElevenSquare.Tasks.T07.TightCover3
import ElevenSquare.Cover

/-! A strict improvement of the uniform covering radius, proved by rational
dyadic leaves. The original 0.173 cover remains untouched. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare
noncomputable section

theorem tight_unit_box_covered : TightBoxCovered 0 0 1 := by
  apply tightBoxCovered_split
  · simpa using tightQuadrant0
  · simpa using tightQuadrant1
  · simpa using tightQuadrant2
  · simpa using tightQuadrant3

theorem closedCell_radius_tight {i : Fin 16} {p : Point}
    (hp : ClosedCell i p) :
    coordinateDistanceSq p (coverSite i) ≤ (17/100 : ℝ)^2 := by
  obtain ⟨j, hj⟩ := tight_unit_box_covered p hp.1.1
    (by simpa using hp.1.2.1) hp.1.2.2.1 (by simpa using hp.1.2.2.2)
  exact le_trans (hp.2 j) hj

end
end ElevenSquare.Tasks.T07
