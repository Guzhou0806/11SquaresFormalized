import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair01Leaf002
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair01Leaf003
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair01Leaf004
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Region001
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Region009

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair01Node001_checked : pair01Node001.Check pair01Source001 pair01Targets := by
  refine ⟨pair01Node002_checked, ?_⟩
  have he : baselineFlip ⟨(381999999999612291640997718582269/98173626953125000000000000000000000), (-100138625999898364967646064942311742467/100529794000000000000000000000000000000), (-1162168480819455734769381142616439997952937645327768595143423930946918684791/808499158534594880000000000000000000000000000000000000000000000000000000000)⟩ :: pair01Source001 = pair01Source003 := by
    norm_num [baselineFlip, pair01Source001, pair01Source003]
  change pair01Node003.Check (baselineFlip ⟨(381999999999612291640997718582269/98173626953125000000000000000000000), (-100138625999898364967646064942311742467/100529794000000000000000000000000000000), (-1162168480819455734769381142616439997952937645327768595143423930946918684791/808499158534594880000000000000000000000000000000000000000000000000000000000)⟩ :: pair01Source001) pair01Targets
  rw [he]
  exact pair01Node003_checked

theorem pair01Node000_checked : pair01Node000.Check pair01Source000 pair01Targets := by
  refine ⟨pair01Node001_checked, ?_⟩
  have he : baselineFlip ⟨(-204335393840693865162618180829/3820000000000000000000000000000), (-63196599378422598895493459043/3820000000000000000000000000000), (-607214257374273766150432812722910353561411736395007775199111367153/12000744158750000000000000000000000000000000000000000000000000000000)⟩ :: pair01Source000 = pair01Source004 := by
    norm_num [baselineFlip, pair01Source000, pair01Source004]
  change pair01Node004.Check (baselineFlip ⟨(-204335393840693865162618180829/3820000000000000000000000000000), (-63196599378422598895493459043/3820000000000000000000000000000), (-607214257374273766150432812722910353561411736395007775199111367153/12000744158750000000000000000000000000000000000000000000000000000000)⟩ :: pair01Source000) pair01Targets
  rw [he]
  exact pair01Node004_checked

theorem pair01_checked : CaptureCoverCheck inputRow pair01Plan pair01Node000 := by
  refine ⟨pair01Node000_checked, ?_⟩
  intro item hi
  simp only [pair01Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact region001_checked
  · exact region009_checked

theorem pair01_capture_or_owned (q : UnitSquare) (hq : inputRow.contains q)
    (hforbidden : ∀ j ∈ pair01Plan, j.1 ≠ feature001 →
      ¬ ∃ p ∈ rationalHull j.1, OpenSquare q p) :
    ∃ p ∈ rationalHull feature001, OpenSquare q p := by
  obtain ⟨item, hi, p, hp, ho⟩ := checked_capture_cover inputRow pair01Plan pair01Node000 pair01_checked q hq
  by_cases he : item.1 = feature001
  · exact ⟨p, he ▸ hp, ho⟩
  · exact False.elim (hforbidden item hi he ⟨p, hp, ho⟩)

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
