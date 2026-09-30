import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair00Leaf002
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair00Leaf003
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair00Leaf004
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Region000
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Region009

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair00Node001_checked : pair00Node001.Check pair00Source001 pair00Targets := by
  refine ⟨pair00Node002_checked, ?_⟩
  have he : baselineFlip ⟨(381999999999612291640997718582269/98173626953125000000000000000000000), (-100138625999898364967646064942311742467/100529794000000000000000000000000000000), (-1125455629479242250451699910747997443305296957970838900129322445225994477199/808499158534594880000000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source001 = pair00Source003 := by
    norm_num [baselineFlip, pair00Source001, pair00Source003]
  change pair00Node003.Check (baselineFlip ⟨(381999999999612291640997718582269/98173626953125000000000000000000000), (-100138625999898364967646064942311742467/100529794000000000000000000000000000000), (-1125455629479242250451699910747997443305296957970838900129322445225994477199/808499158534594880000000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source001) pair00Targets
  rw [he]
  exact pair00Node003_checked

theorem pair00Node000_checked : pair00Node000.Check pair00Source000 pair00Targets := by
  refine ⟨pair00Node001_checked, ?_⟩
  have he : baselineFlip ⟨(-172788692124586204836209472577/3820000000000000000000000000000), (-345577383861464050670137527423/3820000000000000000000000000000), (-1839644050691523223273857614243739758929101503274891978910552225191/12000744158750000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source000 = pair00Source004 := by
    norm_num [baselineFlip, pair00Source000, pair00Source004]
  change pair00Node004.Check (baselineFlip ⟨(-172788692124586204836209472577/3820000000000000000000000000000), (-345577383861464050670137527423/3820000000000000000000000000000), (-1839644050691523223273857614243739758929101503274891978910552225191/12000744158750000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source000) pair00Targets
  rw [he]
  exact pair00Node004_checked

theorem pair00_checked : CaptureCoverCheck inputRow pair00Plan pair00Node000 := by
  refine ⟨pair00Node000_checked, ?_⟩
  intro item hi
  simp only [pair00Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact region000_checked
  · exact region009_checked

theorem pair00_capture_or_owned (q : UnitSquare) (hq : inputRow.contains q)
    (hforbidden : ∀ j ∈ pair00Plan, j.1 ≠ feature000 →
      ¬ ∃ p ∈ rationalHull j.1, OpenSquare q p) :
    ∃ p ∈ rationalHull feature000, OpenSquare q p := by
  obtain ⟨item, hi, p, hp, ho⟩ := checked_capture_cover inputRow pair00Plan pair00Node000 pair00_checked q hq
  by_cases he : item.1 = feature000
  · exact ⟨p, he ▸ hp, ho⟩
  · exact False.elim (hforbidden item hi he ⟨p, hp, ho⟩)

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
