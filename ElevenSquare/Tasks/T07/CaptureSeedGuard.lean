import ElevenSquare.Tasks.T07.CaptureSeedCounterexample
import Mathlib.Tactic.NormNum

/-! One exact geometric explanation of why the standalone cell-0 counterpose
disappears during phase-2 replay: it contains a point promoted for cell 1 in
round 1. The ownership of this point remains a separate promotion obligation. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def round1Cell1Point : QPoint := (124193319/100000000, 85368153/100000000)

theorem seedCounterSquare_hits_round1_cell1_point :
    OpenSquare seedCounterSquare
      ((realPoint round1Cell1Point).1/fieldScale,
        (realPoint round1Cell1Point).2/fieldScale) := by
  norm_num [OpenSquare, localX, localY, dot, perp, seedCounterSquare,
    round1Cell1Point, realPoint, fieldScale, coverCap]
  constructor <;> apply abs_lt.mpr <;> constructor <;> norm_num

end
end ElevenSquare.Tasks.T07
