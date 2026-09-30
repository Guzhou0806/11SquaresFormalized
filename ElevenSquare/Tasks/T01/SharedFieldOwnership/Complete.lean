import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell00
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell01
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell02
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell03
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell04
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell05
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell06
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell07
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell08
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell09
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell10
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell11
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell12
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell13
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell14
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell15

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The 188 exact normalized ownership points in their original gate order. -/
def sharedRoster (cell : Fin 16) : List QPoint :=
  if cell.val = 0 then sharedRosterCell00 else
  if cell.val = 1 then sharedRosterCell01 else
  if cell.val = 2 then sharedRosterCell02 else
  if cell.val = 3 then sharedRosterCell03 else
  if cell.val = 4 then sharedRosterCell04 else
  if cell.val = 5 then sharedRosterCell05 else
  if cell.val = 6 then sharedRosterCell06 else
  if cell.val = 7 then sharedRosterCell07 else
  if cell.val = 8 then sharedRosterCell08 else
  if cell.val = 9 then sharedRosterCell09 else
  if cell.val = 10 then sharedRosterCell10 else
  if cell.val = 11 then sharedRosterCell11 else
  if cell.val = 12 then sharedRosterCell12 else
  if cell.val = 13 then sharedRosterCell13 else
  if cell.val = 14 then sharedRosterCell14 else
  sharedRosterCell15

/-- Every shared field point is strictly owned throughout its full cell chart. -/
theorem shared_roster_full_chart (cell : Fin 16) (q : UnitSquare)
    (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRoster cell, OpenSquare q (realPoint p) := by
  fin_cases cell
  · change ∀ p ∈ sharedRosterCell00, OpenSquare q (realPoint p)
    exact sharedRosterCell00_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell01, OpenSquare q (realPoint p)
    exact sharedRosterCell01_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell02, OpenSquare q (realPoint p)
    exact sharedRosterCell02_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell03, OpenSquare q (realPoint p)
    exact sharedRosterCell03_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell04, OpenSquare q (realPoint p)
    exact sharedRosterCell04_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell05, OpenSquare q (realPoint p)
    exact sharedRosterCell05_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell06, OpenSquare q (realPoint p)
    exact sharedRosterCell06_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell07, OpenSquare q (realPoint p)
    exact sharedRosterCell07_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell08, OpenSquare q (realPoint p)
    exact sharedRosterCell08_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell09, OpenSquare q (realPoint p)
    exact sharedRosterCell09_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell10, OpenSquare q (realPoint p)
    exact sharedRosterCell10_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell11, OpenSquare q (realPoint p)
    exact sharedRosterCell11_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell12, OpenSquare q (realPoint p)
    exact sharedRosterCell12_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell13, OpenSquare q (realPoint p)
    exact sharedRosterCell13_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell14, OpenSquare q (realPoint p)
    exact sharedRosterCell14_owned q hcell hcont hchart
  · change ∀ p ∈ sharedRosterCell15, OpenSquare q (realPoint p)
    exact sharedRosterCell15_owned q hcell hcont hchart

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.shared_roster_full_chart
