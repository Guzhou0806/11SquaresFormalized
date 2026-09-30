import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block000
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block001
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block002
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block003
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block004
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block005
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block006
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Block007

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070CoarseTerminal
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots
noncomputable section

def terminalPlan : List (PoseRow × RowPruningCertificate) := [
  (G070Block000.sourceRow, G070Block000.certificate),
  (G070Block001.sourceRow, G070Block001.certificate),
  (G070Block002.sourceRow, G070Block002.certificate),
  (G070Block003.sourceRow, G070Block003.certificate),
  (G070Block004.sourceRow, G070Block004.certificate),
  (G070Block005.sourceRow, G070Block005.certificate),
  (G070Block006.sourceRow, G070Block006.certificate),
  (G070Block007.sourceRow, G070Block007.certificate)]

theorem terminalPlan_inputs :
    terminalPlan.map Prod.fst = slabRows 8 (14 : Fin 16) := by
  have hrange : (List.finRange 8 : List (Fin 8)) =
      [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  simp only [terminalPlan, slabRows, hrange, List.map_cons, List.map_nil]
  rw [← G070Block000.source_matches, ← G070Block001.source_matches,
    ← G070Block002.source_matches, ← G070Block003.source_matches,
    ← G070Block004.source_matches, ← G070Block005.source_matches,
    ← G070Block006.source_matches, ← G070Block007.source_matches]
  rfl

theorem terminal_checked (s : PoseState)
    (hrows : terminalPlan.map Prod.fst = s.rows (10 : Owner))
    (h11 : s.owned (8 : Owner) = G070Block000.owned0)
    (h10 : s.owned (7 : Owner) = G070Block000.owned1) :
    VerifiedStep s (replaceRows s (10 : Owner) []) := by
  have hc : ∀ item ∈ terminalPlan,
      item.2.Check s (10 : Owner) item.1 := by
    intro item hi
    simp only [terminalPlan, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact G070Block000.row_checked s h11 h10
    · exact G070Block001.row_checked s (by simpa only [G070Block001.owned0, G070Block000.owned0] using h11)
        (by simpa only [G070Block001.owned1, G070Block000.owned1] using h10)
    · exact G070Block002.row_checked s (by simpa only [G070Block002.owned0, G070Block000.owned0] using h11)
        (by simpa only [G070Block002.owned1, G070Block000.owned1] using h10)
    · exact G070Block003.row_checked s (by simpa only [G070Block003.owned0, G070Block000.owned1] using h10)
    · exact G070Block004.row_checked s (by simpa only [G070Block004.owned0, G070Block000.owned1] using h10)
    · exact G070Block005.row_checked s (by simpa only [G070Block005.owned0, G070Block000.owned1] using h10)
    · exact G070Block006.row_checked s (by simpa only [G070Block006.owned0, G070Block000.owned1] using h10)
    · exact G070Block007.row_checked s (by simpa only [G070Block007.owned0, G070Block000.owned0] using h11)
        (by simpa only [G070Block007.owned1, G070Block000.owned1] using h10)
  have hout : pruningOutput terminalPlan = [] := by rfl
  simpa only [hout] using checked_pruning_step s (10 : Owner)
    terminalPlan hrows hc

#print axioms terminalPlan_inputs
#print axioms terminal_checked

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070CoarseTerminal
