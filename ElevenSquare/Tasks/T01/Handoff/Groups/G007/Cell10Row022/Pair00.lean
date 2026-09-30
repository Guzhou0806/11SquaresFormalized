import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Pair00Leaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Pair00Leaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Pair00Leaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Region003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Region082
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Region092

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair00Node001_checked : pair00Node001.Check pair00Source001 pair00Targets := by
  refine ⟨pair00Node002_checked, ?_⟩
  have he : baselineFlip ⟨(298252993999697290107666865744322420323/899882366000000000000000000000000000000), (1296125999998684505537905259149638717/1406066196875000000000000000000000000), (5300243565324167312000262817192365220117258613201483369687028579697643915654729/1619576545275515912000000000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source001 = pair00Source003 := by
    norm_num [baselineFlip, pair00Source001, pair00Source003]
  change pair00Node003.Check (baselineFlip ⟨(298252993999697290107666865744322420323/899882366000000000000000000000000000000), (1296125999998684505537905259149638717/1406066196875000000000000000000000000), (5300243565324167312000262817192365220117258613201483369687028579697643915654729/1619576545275515912000000000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source001) pair00Targets
  rw [he]
  exact pair00Node003_checked

theorem pair00Node000_checked : pair00Node000.Check pair00Source000 pair00Targets := by
  refine ⟨pair00Node001_checked, ?_⟩
  have he : baselineFlip ⟨(1296125999998684505537905259149638717/1406066196875000000000000000000000000), (-298252993999697290107666865744322420323/899882366000000000000000000000000000000), (2419024488058329284095422846011388584919809240031625173510617657023862790374129/1619576545275515912000000000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source000 = pair00Source004 := by
    norm_num [baselineFlip, pair00Source000, pair00Source004]
  change pair00Node004.Check (baselineFlip ⟨(1296125999998684505537905259149638717/1406066196875000000000000000000000000), (-298252993999697290107666865744322420323/899882366000000000000000000000000000000), (2419024488058329284095422846011388584919809240031625173510617657023862790374129/1619576545275515912000000000000000000000000000000000000000000000000000000000000)⟩ :: pair00Source000) pair00Targets
  rw [he]
  exact pair00Node004_checked

theorem pair00_checked : CaptureCoverCheck inputRow pair00Plan pair00Node000 := by
  refine ⟨pair00Node000_checked, ?_⟩
  intro item hi
  simp only [pair00Plan, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact region003_checked
  · exact region082_checked
  · exact region092_checked

theorem pair00_capture_or_owned (q : UnitSquare) (hq : inputRow.contains q)
    (hforbidden : ∀ j ∈ pair00Plan, j.1 ≠ feature000 →
      ¬ ∃ p ∈ rationalHull j.1, OpenSquare q p) :
    ∃ p ∈ rationalHull feature000, OpenSquare q p := by
  obtain ⟨item, hi, p, hp, ho⟩ := checked_capture_cover inputRow pair00Plan pair00Node000 pair00_checked q hq
  by_cases he : item.1 = feature000
  · exact ⟨p, he ▸ hp, ho⟩
  · exact False.elim (hforbidden item hi he ⟨p, hp, ho⟩)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
