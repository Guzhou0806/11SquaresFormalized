import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime000.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime001.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime002.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime003.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime004.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime005.MedianAggregate

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

/-- The first feature B target has one polygon over a broad interval. Its
median witness is selected from three checked closed chart pieces. -/
theorem featureB_early (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) (hlt : (0 : ℝ) ≤ t)
    (htu : t ≤ (31/64 : ℝ))
    (hcontains : SymbolicPolygonContains
      SymbolicCell00.Regime000.target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  by_cases h0 : t ≤ (7/2048 : ℝ)
  · apply SymbolicCell00.Regime000.majority_of_target q t ha
    · simpa [SymbolicCell00.Regime000.left] using hlt
    · simpa [SymbolicCell00.Regime000.right] using h0
    · exact hcontains
  by_cases h1 : t ≤ (15/4096 : ℝ)
  · apply SymbolicCell00.ConeGap000.majority_of_target q t ha
    · have : (7/2048 : ℝ) ≤ t := le_of_lt (lt_of_not_ge h0)
      simpa [SymbolicCell00.ConeGap000.left] using this
    · simpa [SymbolicCell00.ConeGap000.right] using h1
    · simpa only [show SymbolicCell00.ConeGap000.target =
        SymbolicCell00.Regime000.target from rfl] using hcontains
  · apply SymbolicCell00.Regime001.majority_of_target q t ha
    · have : (15/4096 : ℝ) ≤ t := le_of_lt (lt_of_not_ge h1)
      simpa [SymbolicCell00.Regime001.left] using this
    · have : t ≤ (255/512 : ℝ) := by linarith
      simpa [SymbolicCell00.Regime001.right] using this
    · simpa only [show SymbolicCell00.Regime001.target =
        SymbolicCell00.Regime000.target from rfl] using hcontains

theorem featureB_middle (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (1/2 : ℝ) ≤ t) (htu : t ≤ (19/32 : ℝ))
    (hcontains : SymbolicPolygonContains
      SymbolicCell00.Regime002.target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  apply SymbolicCell00.Regime002.majority_of_target q t ha
  · have : (2041/4096 : ℝ) ≤ t := by linarith
    simpa [SymbolicCell00.Regime002.left] using this
  · have : t ≤ (85/128 : ℝ) := by linarith
    simpa [SymbolicCell00.Regime002.right] using this
  · exact hcontains

theorem featureB_late (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (11/16 : ℝ) ≤ t) (htu : t ≤ (499/512 : ℝ))
    (hcontains : SymbolicPolygonContains
      SymbolicCell00.Regime003.target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  by_cases h0 : t ≤ (2973/4096 : ℝ)
  · apply SymbolicCell00.Regime003.majority_of_target q t ha
    · have : (2721/4096 : ℝ) ≤ t := by linarith
      simpa [SymbolicCell00.Regime003.left] using this
    · simpa [SymbolicCell00.Regime003.right] using h0
    · exact hcontains
  by_cases h1 : t ≤ (1487/2048 : ℝ)
  · apply SymbolicCell00.ConeGap003.majority_of_target q t ha
    · have : (2973/4096 : ℝ) ≤ t := le_of_lt (lt_of_not_ge h0)
      simpa [SymbolicCell00.ConeGap003.left] using this
    · simpa [SymbolicCell00.ConeGap003.right] using h1
    · simpa only [show SymbolicCell00.ConeGap003.target =
        SymbolicCell00.Regime003.target from rfl] using hcontains
  · apply SymbolicCell00.Regime004.majority_of_target q t ha
    · have : (1487/2048 : ℝ) ≤ t := le_of_lt (lt_of_not_ge h1)
      simpa [SymbolicCell00.Regime004.left] using this
    · have : t ≤ (1997/2048 : ℝ) := by linarith
      simpa [SymbolicCell00.Regime004.right] using this
    · simpa only [show SymbolicCell00.Regime004.target =
        SymbolicCell00.Regime003.target from rfl] using hcontains

theorem featureB_end (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (125/128 : ℝ) ≤ t) (htu : t ≤ (1 : ℝ))
    (hcontains : SymbolicPolygonContains
      SymbolicCell00.Regime005.target t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  apply SymbolicCell00.Regime005.majority_of_target q t ha
  · have : (3995/4096 : ℝ) ≤ t := by linarith
    simpa [SymbolicCell00.Regime005.left] using this
  · simpa [SymbolicCell00.Regime005.right] using htu
  · exact hcontains

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.featureB_early
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.featureB_middle
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.featureB_late
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.featureB_end
