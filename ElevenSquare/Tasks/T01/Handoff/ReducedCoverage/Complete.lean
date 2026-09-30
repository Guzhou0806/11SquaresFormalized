import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G013
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G014
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G016
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G017
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G022
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G024
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G028
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G029
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G030
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G032
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G034
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G042
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G049
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G051
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G054
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G059
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G060
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G061
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G062
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G073
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G075
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.G087
import ElevenSquare.Tasks.T01.Handoff.Coverage
namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff

theorem every_group_covered (g : Group) : Covered g := by
  rcases group_partition g with hs | ho
  · exact fun k hk => ⟨g, hs, hk⟩
  · simp only [omittedGroups, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact G013.covers
    · exact G014.covers
    · exact G016.covers
    · exact G017.covers
    · exact G022.covers
    · exact G024.covers
    · exact G028.covers
    · exact G029.covers
    · exact G030.covers
    · exact G032.covers
    · exact G034.covers
    · exact G042.covers
    · exact G049.covers
    · exact G051.covers
    · exact G054.covers
    · exact G059.covers
    · exact G060.covers
    · exact G061.covers
    · exact G062.covers
    · exact G073.covers
    · exact G075.covers
    · exact G087.covers

/-- All 1,931 public baseline cases are covered by the selected 71 groups. -/
theorem inventory_covered (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    ∃ g : Group, Selected g ∧ k.val ∈ groupCases g := by
  obtain ⟨g, hg⟩ := ElevenSquare.Tasks.T01.Handoff.inventory_covered k hk
  exact every_group_covered g k.val hg

end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage

#print axioms ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.inventory_covered
