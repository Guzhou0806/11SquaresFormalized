import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair02Leaf002
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair02Leaf003
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair02Leaf004
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Region002
import ElevenSquare.Tasks.T01.Field03Cell04Row000.Region009

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair02Node001_checked : pair02Node001.Check pair02Source001 pair02Targets := by
  refine ⟨pair02Node002_checked, ?_⟩
  have he : baselineFlip ⟨(381999999999612291640997718582269/98173626953125000000000000000000000), (-100138625999898364967646064942311742467/100529794000000000000000000000000000000), (-1125455629479242250451699910747997443305296957970838900129322445225994477199/808499158534594880000000000000000000000000000000000000000000000000000000000)⟩ :: pair02Source001 = pair02Source003 := by
    norm_num [baselineFlip, pair02Source001, pair02Source003]
  change pair02Node003.Check (baselineFlip ⟨(381999999999612291640997718582269/98173626953125000000000000000000000), (-100138625999898364967646064942311742467/100529794000000000000000000000000000000), (-1125455629479242250451699910747997443305296957970838900129322445225994477199/808499158534594880000000000000000000000000000000000000000000000000000000000)⟩ :: pair02Source001) pair02Targets
  rw [he]
  exact pair02Node003_checked

theorem pair02Node000_checked : pair02Node000.Check pair02Source000 pair02Targets := by
  refine ⟨pair02Node001_checked, ?_⟩
  have he : baselineFlip ⟨(-188562042982640034999413826703/1910000000000000000000000000000), (-204386991619943324782815493233/1910000000000000000000000000000), (-311993811790913193384316044913188542514337530750449355573364266993/1500093019843750000000000000000000000000000000000000000000000000000)⟩ :: pair02Source000 = pair02Source004 := by
    norm_num [baselineFlip, pair02Source000, pair02Source004]
  change pair02Node004.Check (baselineFlip ⟨(-188562042982640034999413826703/1910000000000000000000000000000), (-204386991619943324782815493233/1910000000000000000000000000000), (-311993811790913193384316044913188542514337530750449355573364266993/1500093019843750000000000000000000000000000000000000000000000000000)⟩ :: pair02Source000) pair02Targets
  rw [he]
  exact pair02Node004_checked

theorem pair02_checked : CaptureCoverCheck inputRow pair02Plan pair02Node000 := by
  refine ⟨pair02Node000_checked, ?_⟩
  intro item hi
  simp only [pair02Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact region002_checked
  · exact region009_checked

theorem pair02_capture_or_owned (q : UnitSquare) (hq : inputRow.contains q)
    (hforbidden : ∀ j ∈ pair02Plan, j.1 ≠ feature002 →
      ¬ ∃ p ∈ rationalHull j.1, OpenSquare q p) :
    ∃ p ∈ rationalHull feature002, OpenSquare q p := by
  obtain ⟨item, hi, p, hp, ho⟩ := checked_capture_cover inputRow pair02Plan pair02Node000 pair02_checked q hq
  by_cases he : item.1 = feature002
  · exact ⟨p, he ▸ hp, ho⟩
  · exact False.elim (hforbidden item hi he ⟨p, hp, ho⟩)

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
