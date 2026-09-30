import ElevenSquare.Tasks.T07.LocalTerminalBridge
import ElevenSquare.Tasks.T07.LocalCoreFitsRow1Bridge
import ElevenSquare.Tasks.T07.LocalTraceTerminalHullBatch00
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairBatch00

/-! One complete terminal prune step, conditional only on the actual source
row and the two prior promoted owned hulls. These ancestry premises are not
established by the occupied-cell seed. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal1_prune_of_source_hulls (s : PoseState)
    (hrow : s.rows (5 : Owner) = [terminal1PhysicalPoseRow])
    (h9 : rationalHull (terminalPairOwner9.map qpointFieldNormalize) ⊆
      rationalHull (s.owned (6 : Owner)))
    (h13 : rationalHull (terminalPairOwner13.map qpointFieldNormalize) ⊆
      rationalHull (s.owned (9 : Owner))) :
    VerifiedStep s (replaceRows s (5 : Owner) []) := by
  apply terminal_prune_of_rowwise_field_covers s (5 : Owner)
    (fun _ => terminal1Domain)
    (fun _ => [terminal1Triangle0, terminal1Triangle1])
  · intro r hr q hqr
    rw [hrow] at hr
    simp only [List.mem_singleton] at hr
    subst r
    exact terminal1PhysicalPoseRow_source q hqr
  · intro _r _hr
    exact terminal1_cover_cert
  · intro r hr region hregion
    rw [hrow] at hr
    simp only [List.mem_singleton] at hr
    subst r
    simp only [List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hregion
    rcases hregion with rfl | rfl
    · refine ⟨(6 : Owner), terminalPairOwner9, terminal1CoreField,
        terminal1Triangle0Vertices, by decide, ?_, ?_, h9, ?_⟩
      · exact fun p hp => terminal1_triangle0_in_hull p hp
      · exact terminal1Triangle0_vertex_pairs
      · exact fun q hq => terminal1PhysicalPoseRow_coreFits q hq
    · refine ⟨(9 : Owner), terminalPairOwner13, terminal1CoreField,
        terminal1Triangle1Vertices, by decide, ?_, ?_, h13, ?_⟩
      · exact fun p hp => terminal1_triangle1_in_hull p hp
      · exact terminal1Triangle1_vertex_pairs
      · exact fun q hq => terminal1PhysicalPoseRow_coreFits q hq

end
end ElevenSquare.Tasks.T07
