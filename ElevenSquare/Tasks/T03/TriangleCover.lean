import ElevenSquare.Tasks.T03.LinearCover
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

namespace ElevenSquare.Pending.T03
noncomputable section
open scoped BigOperators

def orientedCross (a b p : Point) : ℝ :=
  (b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1)

theorem convex_three_mem (F : Set Point) (hF : Convex ℝ F) (a b c : Point)
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (u v w : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hs : u+v+w=1) :
    u • a+v • b+w • c ∈ F := by
  let weights : Fin 3 → ℝ := ![u,v,w]
  let vertices : Fin 3 → Point := ![a,b,c]
  have h := hF.sum_mem (t := Finset.univ) (w := weights) (z := vertices)
    (by
      intro i _
      fin_cases i
      · exact hu
      · exact hv
      · exact hw)
    (by simpa [weights,Fin.sum_univ_succ,add_assoc] using hs)
    (by intro i _; fin_cases i <;> simp [vertices,ha,hb,hc])
  simpa [weights,vertices,Fin.sum_univ_succ,add_assoc] using h

/-- Nonnegative barycentric coordinates include every edge and vertex. -/
theorem triangle_mem_convex (F : Set Point) (hF : Convex ℝ F) (a b c p : Point)
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F)
    (hD : 0 < orientedCross a b c)
    (hab : 0 ≤ orientedCross a b p) (hbc : 0 ≤ orientedCross b c p)
    (hca : 0 ≤ orientedCross c a p) : p ∈ F := by
  let u := orientedCross b c p / orientedCross a b c
  let v := orientedCross c a p / orientedCross a b c
  let w := orientedCross a b p / orientedCross a b c
  have hu : 0 ≤ u := div_nonneg hbc hD.le
  have hv : 0 ≤ v := div_nonneg hca hD.le
  have hw : 0 ≤ w := div_nonneg hab hD.le
  have hs : u+v+w=1 := by
    dsimp [u,v,w]
    field_simp [ne_of_gt hD]
    dsimp [orientedCross]
    ring
  have hp : u • a+v • b+w • c = p := by
    ext <;> dsimp [u,v,w]
    all_goals field_simp [ne_of_gt hD]
    all_goals dsimp [orientedCross]; ring
  rw [← hp]
  exact convex_three_mem F hF a b c ha hb hc u v w hu hv hw hs

theorem rational_triangle_mem (a b c : QPoint) (p : Point)
    (hD : 0 < orientedCross (realPoint a) (realPoint b) (realPoint c))
    (hab : 0 ≤ orientedCross (realPoint a) (realPoint b) p)
    (hbc : 0 ≤ orientedCross (realPoint b) (realPoint c) p)
    (hca : 0 ≤ orientedCross (realPoint c) (realPoint a) p) :
    p ∈ rationalHull [a,b,c] := by
  have ha : realPoint a ∈ rationalHull [a,b,c] := subset_convexHull ℝ _ ⟨a,by simp,rfl⟩
  have hb : realPoint b ∈ rationalHull [a,b,c] := subset_convexHull ℝ _ ⟨b,by simp,rfl⟩
  have hc : realPoint c ∈ rationalHull [a,b,c] := subset_convexHull ℝ _ ⟨c,by simp,rfl⟩
  exact triangle_mem_convex (rationalHull [a,b,c]) (convex_convexHull ℝ _)
    (realPoint a) (realPoint b) (realPoint c) p ha hb hc hD hab hbc hca

end
end ElevenSquare.Pending.T03
