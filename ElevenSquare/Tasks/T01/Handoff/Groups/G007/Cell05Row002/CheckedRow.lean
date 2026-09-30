import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row002.Cover00
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row002.Cover01
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row002.Cover02
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row002.Geometry
import ElevenSquare.Tasks.T01.TripleCapture
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Capacity

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def forbiddenPoints : List QPoint := [((78686667498184714830022331/50000000000000000000000000), (63091593459680811351013693/100000000000000000000000000)), ((1572048057/1000000000), (232270007/250000000)), ((294604953/125000000), (249496063/250000000)), ((857991217/1000000000), (1586351539/1000000000))]

theorem singleton_matches : feature003 = [G007.point] := by
  norm_num [feature003, G007.point, G007.physicalToUnit]

theorem row_choice (q : UnitSquare) (hq : inputRow.contains q)
    (hblocked : ∀ p ∈ forbiddenPoints, ¬ OpenSquare q (realPoint p)) :
    OpenSquare q (realPoint G007.point) ∨ BaselineMajorityCapture G007.sites 2 q := by
  by_cases hpoint : OpenSquare q (realPoint G007.point)
  · exact Or.inl hpoint
  right
  have hp0 : ∃ p ∈ rationalHull feature000, OpenSquare q p := by
    apply pair00_capture_or_owned q hq
    intro item hi hne hc
    simp only [pair00Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hne rfl
    · exact hblocked ((1572048057/1000000000), (232270007/250000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((294604953/125000000), (249496063/250000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((857991217/1000000000), (1586351539/1000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
  have hp1 : ∃ p ∈ rationalHull feature001, OpenSquare q p := by
    apply pair01_capture_or_owned q hq
    intro item hi hne hc
    simp only [pair01Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hne rfl
    · exact hblocked ((78686667498184714830022331/50000000000000000000000000), (63091593459680811351013693/100000000000000000000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((1572048057/1000000000), (232270007/250000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((857991217/1000000000), (1586351539/1000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
  have hp2 : ∃ p ∈ rationalHull feature002, OpenSquare q p := by
    apply pair02_capture_or_owned q hq
    intro item hi hne hc
    simp only [pair02Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hne rfl
    · exact hblocked ((78686667498184714830022331/50000000000000000000000000), (63091593459680811351013693/100000000000000000000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((1572048057/1000000000), (232270007/250000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((857991217/1000000000), (1586351539/1000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
  have hm := triple_majority_capture ((18222292873107226633357/10000000000000000000000), (1163125077006844253193/625000000000000000000)) ((1542115123823788708187676321551/955000000000000000000000000000), (6837472683049384192055091322527/3820000000000000000000000000000)) ((6837472683049384192055091322527/3820000000000000000000000000000), (1542115123823788708187676321551/955000000000000000000000000000)) q hp0 hp1 hp2
  convert hm using 1 <;> norm_num [sites, site0, site1, site2, physicalToUnit]

/-- Every forbidden point must already belong to a distinct actual square. -/
theorem packing_row_choice {S : ℝ} (P : Packing 11 S) (i : Owner)
    (hq : inputRow.contains (P.squares i))
    (howned : ∀ p ∈ forbiddenPoints, ∃ j : Owner, i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    OpenSquare (P.squares i) (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 (P.squares i) := by
  apply row_choice _ hq
  intro p hp ho
  obtain ⟨j, hij, hj⟩ := howned p hp
  exact P.interior_disjoint i j hij (realPoint p) ⟨ho,hj⟩

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row002
