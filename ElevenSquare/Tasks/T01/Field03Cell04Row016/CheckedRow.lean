import ElevenSquare.Tasks.T01.Field03Cell04Row016.Cover00
import ElevenSquare.Tasks.T01.Field03Cell04Row016.Cover01
import ElevenSquare.Tasks.T01.Field03Cell04Row016.Cover02
import ElevenSquare.Tasks.T01.Field03Cell04Row016.Geometry
import ElevenSquare.Tasks.T01.TripleCapture
import ElevenSquare.Tasks.T01.Field03Feature

namespace ElevenSquare.Tasks.T01.Field03Cell04Row016
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def forbiddenPoints : List QPoint := [((80206788320008528328995421/100000000000000000000000000), (176483527032089485245355847/200000000000000000000000000)), ((498020679/500000000), (997648353/1000000000)), ((386169321/500000000), (997648353/1000000000))]

theorem row_majority (q : UnitSquare) (hq : inputRow.contains q)
    (hblocked : ∀ p ∈ forbiddenPoints, ¬ OpenSquare q (realPoint p)) :
    BaselineMajorityCapture baselineField03Sites 2 q := by
  have hp0 : ∃ p ∈ rationalHull feature000, OpenSquare q p := by
    apply pair00_capture_or_owned q hq
    intro item hi hne hc
    simp only [pair00Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hne rfl
    · exact hblocked ((80206788320008528328995421/100000000000000000000000000), (176483527032089485245355847/200000000000000000000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((498020679/500000000), (997648353/1000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((386169321/500000000), (997648353/1000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
  have hp1 : ∃ p ∈ rationalHull feature001, OpenSquare q p := by
    apply pair01_capture_or_owned q hq
    intro item hi hne hc
    simp only [pair01Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hne rfl
    · exact hblocked ((498020679/500000000), (997648353/1000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
  have hp2 : ∃ p ∈ rationalHull feature002, OpenSquare q p := by
    apply pair02_capture_or_owned q hq
    intro item hi hne hc
    simp only [pair02Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hne rfl
    · exact hblocked ((80206788320008528328995421/100000000000000000000000000), (176483527032089485245355847/200000000000000000000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
    · exact hblocked ((498020679/500000000), (997648353/1000000000)) (by simp [forbiddenPoints])
        (singleton_capture _ q hc)
  have hm := triple_majority_capture ((3801351224026937993380638472577/3820000000000000000000000000000), (7429913755929289781925067472577/3820000000000000000000000000000)) ((2713958513015969924117/2500000000000000000000), (18997709591111789468819/10000000000000000000000)) ((1869077312324257697242572506767/1910000000000000000000000000000), (3817124574884991823543842826703/1910000000000000000000000000000)) q hp0 hp1 hp2
  convert hm using 1 <;> norm_num [baselineField03Sites]

/-- Every forbidden point must already belong to a distinct actual square. -/
theorem packing_row_majority {S : ℝ} (P : Packing 11 S) (i : Owner)
    (hq : inputRow.contains (P.squares i))
    (howned : ∀ p ∈ forbiddenPoints, ∃ j : Owner, i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  apply row_majority _ hq
  intro p hp ho
  obtain ⟨j, hij, hj⟩ := howned p hp
  exact P.interior_disjoint i j hij (realPoint p) ⟨ho,hj⟩

end
end ElevenSquare.Tasks.T01.Field03Cell04Row016
