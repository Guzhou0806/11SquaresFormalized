import ElevenSquare.Tasks.T02.Prior1000Step001Row055.Data
import ElevenSquare.Tasks.T02.RationalChecks
import ElevenSquare.Tasks.T02.PolygonCorners
import ElevenSquare.Tasks.T02.Prior1000Cores.Row055

namespace ElevenSquare.Tasks.T02.Prior1000Step001Row055.WeightedInteger
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

set_option maxRecDepth 100000
theorem core_checked : ∀ v ∈ coreVertices, BaselineCoreVertexCheck v inputRow.lo inputRow.hi := by
  exact ElevenSquare.Tasks.T02.Prior1000Cores.Row055.core_checked
def piece0Corners : List PolygonCorner := [⟨15, 1, 15, 0⟩, ⟨0, 2, 0, 1⟩, ⟨1, 3, 1, 2⟩, ⟨2, 4, 2, 3⟩, ⟨3, 5, 3, 4⟩, ⟨4, 6, 4, 5⟩, ⟨5, 7, 5, 6⟩, ⟨6, 8, 6, 7⟩, ⟨7, 9, 7, 8⟩, ⟨8, 10, 8, 9⟩, ⟨9, 11, 9, 10⟩, ⟨10, 12, 10, 11⟩, ⟨11, 13, 11, 12⟩, ⟨12, 14, 12, 13⟩, ⟨13, 15, 13, 14⟩, ⟨14, 0, 14, 15⟩]
theorem piece0_checked : piece0.Check checkState (6 : Owner) inputRow := by
  refine ⟨by decide, ?_, ?_, core_checked⟩
  · exact polygon_corners_sound piece0.vertices piece0.polygon piece0Corners (by rational_decide)
  · rational_decide
def piece1Corners : List PolygonCorner := [⟨14, 1, 14, 0⟩, ⟨0, 2, 0, 1⟩, ⟨1, 3, 1, 2⟩, ⟨2, 4, 2, 3⟩, ⟨3, 5, 3, 4⟩, ⟨4, 6, 4, 5⟩, ⟨5, 7, 5, 6⟩, ⟨6, 8, 6, 7⟩, ⟨7, 9, 7, 8⟩, ⟨8, 10, 8, 9⟩, ⟨9, 11, 9, 10⟩, ⟨10, 12, 10, 11⟩, ⟨11, 13, 11, 12⟩, ⟨12, 14, 12, 13⟩, ⟨13, 0, 13, 14⟩]
theorem piece1_checked : piece1.Check checkState (6 : Owner) inputRow := by
  refine ⟨by decide, ?_, ?_, core_checked⟩
  · exact polygon_corners_sound piece1.vertices piece1.polygon piece1Corners (by rational_decide)
  · rational_decide
def piece2Corners : List PolygonCorner := [⟨14, 1, 14, 0⟩, ⟨0, 2, 0, 1⟩, ⟨1, 3, 1, 2⟩, ⟨2, 4, 2, 3⟩, ⟨3, 5, 3, 4⟩, ⟨4, 6, 4, 5⟩, ⟨5, 7, 5, 6⟩, ⟨6, 8, 6, 7⟩, ⟨7, 9, 7, 8⟩, ⟨8, 10, 8, 9⟩, ⟨9, 11, 9, 10⟩, ⟨10, 12, 10, 11⟩, ⟨11, 13, 11, 12⟩, ⟨12, 14, 12, 13⟩, ⟨13, 0, 13, 14⟩]
theorem piece2_checked : piece2.Check checkState (6 : Owner) inputRow := by
  refine ⟨by decide, ?_, ?_, core_checked⟩
  · exact polygon_corners_sound piece2.vertices piece2.polygon piece2Corners (by rational_decide)
  · rational_decide
theorem forbidden_checked : ∀ p ∈ certificate.forbidden, p.Check checkState (6 : Owner) inputRow := by
  intro p hp
  simp only [certificate, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact piece0_checked
  · exact piece1_checked
  · exact piece2_checked

end
end ElevenSquare.Tasks.T02.Prior1000Step001Row055.WeightedInteger
