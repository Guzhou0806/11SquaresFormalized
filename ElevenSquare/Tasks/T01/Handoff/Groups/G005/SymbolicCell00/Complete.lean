import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime000.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime001.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap001.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime002.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime003.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime004.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap004.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianAggregate
import ElevenSquare.Tasks.T01.ClosedWindowCover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def windows : List (ℚ × ℚ) := [
  (Regime000.left, Regime000.right), (ConeGap000.left, ConeGap000.right), (Regime001.left, Regime001.right), (MedianGap001.left, MedianGap001.right), (Regime002.left, Regime002.right), (MedianGap002.left, MedianGap002.right), (Regime003.left, Regime003.right), (ConeGap003.left, ConeGap003.right), (Regime004.left, Regime004.right), (MedianGap004.left, MedianGap004.right), (Regime005.left, Regime005.right)]

theorem windows_checked : ClosedWindowCoverCheck windows := by
  norm_num [windows, ClosedWindowCoverCheck, ClosedWindowChain,
    Regime000.left, Regime000.right, ConeGap000.left, ConeGap000.right, Regime001.left, Regime001.right, MedianGap001.left, MedianGap001.right, Regime002.left, Regime002.right, MedianGap002.left, MedianGap002.right, Regime003.left, Regime003.right, ConeGap003.left, ConeGap003.right, Regime004.left, Regime004.right, MedianGap004.left, MedianGap004.right, Regime005.left, Regime005.right]

theorem captures_square (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    BaselineMajorityCapture G005.featureB 2 q := by
  refine (closed_window_cover_sound windows windows_checked
    (fun u => q.axis = chartAxis u → BaselineMajorityCapture G005.featureB 2 q)
    ?_ t ht0 ht1) ha
  intro w hw u hl hu haxis
  simp only [windows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Regime000.captures_square q u haxis hcont hcell hl hu
  · exact ConeGap000.captures_square q u haxis hcont hcell hl hu
  · exact Regime001.captures_square q u haxis hcont hcell hl hu
  · exact MedianGap001.captures_square q u haxis hcont hcell hl hu
  · exact Regime002.captures_square q u haxis hcont hcell hl hu
  · exact MedianGap002.captures_square q u haxis hcont hcell hl hu
  · exact Regime003.captures_square q u haxis hcont hcell hl hu
  · exact ConeGap003.captures_square q u haxis hcont hcell hl hu
  · exact Regime004.captures_square q u haxis hcont hcell hl hu
  · exact MedianGap004.captures_square q u haxis hcont hcell hl hu
  · exact Regime005.captures_square q u haxis hcont hcell hl hu

theorem capture_from_packing (P : Packing 11 coverCap) (hc : IsCharted P)
    (i : Owner) (hcell : ClosedCell 0 (normalizeCenter (P.squares i).center)) :
    BaselineMajorityCapture G005.featureB 2 (P.squares i) := by
  obtain ⟨t, ht0, ht1, ha⟩ := hc i
  exact captures_square (P.squares i) t ha (P.contained i) hcell ht0 ht1

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.captures_square
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.capture_from_packing
