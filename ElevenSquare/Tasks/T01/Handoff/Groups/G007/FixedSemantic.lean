import ElevenSquare.Tasks.T01.CaptureCover
import ElevenSquare.Tasks.T01.TripleCapture
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Capacity

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedSemantic
open ElevenSquare Pending
noncomputable section

/-- A fixed median target can certify the three pair captures by exact
polygon implications. The pair pieces supply the open-square witnesses. -/
theorem median_target_majority
    (row : PoseRow) (q : UnitSquare) (hq : row.contains q)
    (medianTarget : Polygon)
    (pair01 pair02 pair12 : FeatureCapturePiece)
    (medianToPair01 medianToPair02 medianToPair12 : List BaselineCombination)
    (hpair01 : pair01.Check [G007.site0, G007.site1] row)
    (hpair02 : pair02.Check [G007.site0, G007.site2] row)
    (hpair12 : pair12.Check [G007.site1, G007.site2] row)
    (himp01 : BaselinePolygonImplicationCheck medianTarget pair01.polygon medianToPair01)
    (himp02 : BaselinePolygonImplicationCheck medianTarget pair02.polygon medianToPair02)
    (himp12 : BaselinePolygonImplicationCheck medianTarget pair12.polygon medianToPair12)
    (hmedian : q.center ∈ medianTarget.carrier) :
    BaselineMajorityCapture G007.sites 2 q := by
  have h01 : q.center ∈ pair01.polygon.carrier :=
    baseline_polygon_implication_check_sound _ _ _ himp01 hmedian
  have h02 : q.center ∈ pair02.polygon.carrier :=
    baseline_polygon_implication_check_sound _ _ _ himp02 hmedian
  have h12 : q.center ∈ pair12.polygon.carrier :=
    baseline_polygon_implication_check_sound _ _ _ himp12 hmedian
  have hp01 := feature_capture_piece_sound [G007.site0, G007.site1]
    row pair01 hpair01 q hq h01
  have hp02 := feature_capture_piece_sound [G007.site0, G007.site2]
    row pair02 hpair02 q hq h02
  have hp12 := feature_capture_piece_sound [G007.site1, G007.site2]
    row pair12 hpair12 q hq h12
  simpa only [G007.sites] using
    (triple_majority_capture G007.site0 G007.site1 G007.site2 q
      hp01 hp02 hp12)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedSemantic

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedSemantic.median_target_majority
