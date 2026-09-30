import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def fixed01 : Point := ((site1.2 : ℝ) - site0.2, (site0.1 : ℝ) - site1.1)
def fixed02 : Point := ((site2.2 : ℝ) - site0.2, (site0.1 : ℝ) - site2.1)
def fixed12 : Point := ((site2.2 : ℝ) - site1.2, (site1.1 : ℝ) - site2.1)

theorem fixed01_order :
    dot fixed01 (realPoint site2) ≤ dot fixed01 (realPoint site0) ∧
    dot fixed01 (realPoint site0) = dot fixed01 (realPoint site1) := by
  constructor <;> norm_num [fixed01, site0, site1, site2, dot, realPoint]

theorem fixed02_order :
    dot fixed02 (realPoint site0) = dot fixed02 (realPoint site2) ∧
    dot fixed02 (realPoint site2) ≤ dot fixed02 (realPoint site1) := by
  constructor <;> norm_num [fixed02, site0, site1, site2, dot, realPoint]

theorem fixed12_order :
    dot fixed12 (realPoint site0) ≤ dot fixed12 (realPoint site1) ∧
    dot fixed12 (realPoint site1) = dot fixed12 (realPoint site2) := by
  constructor <;> norm_num [fixed12, site0, site1, site2, dot, realPoint]

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
