import ElevenSquare.Tasks.T07.LocalTriangle
import ElevenSquare.Tasks.T07.LocalMinkowski
import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch00
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A triangle's three exact oriented edge bounds give nonnegative affine
weights.  This converts the archived triangular collision polygons into
genuine rational-hull membership, without trusting polygon metadata. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def cross2 (v w : Point) : ℝ := v.1*w.2-v.2*w.1

theorem rationalHull_triangle_of_edges {vertices : List QPoint}
    (a b c : QPoint) (p : Point)
    (ha : a ∈ vertices) (hb : b ∈ vertices) (hc : c ∈ vertices)
    (hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a))
    (hAB : 0 ≤ cross2 (realPoint b-realPoint a) (p-realPoint a))
    (hBC : 0 ≤ cross2 (realPoint c-realPoint b) (p-realPoint b))
    (hCA : 0 ≤ cross2 (realPoint a-realPoint c) (p-realPoint c)) :
    p ∈ rationalHull vertices := by
  let A := realPoint a
  let B := realPoint b
  let C := realPoint c
  let D := cross2 (B-A) (C-A)
  let nA := cross2 (C-B) (p-B)
  let nB := cross2 (A-C) (p-C)
  let nC := cross2 (B-A) (p-A)
  have hD : 0 < D := hdet
  have hDne : D ≠ 0 := ne_of_gt hD
  have hnA : 0 ≤ nA := hBC
  have hnB : 0 ≤ nB := hCA
  have hnC : 0 ≤ nC := hAB
  have hsumNum : nA+nB+nC=D := by
    dsimp [nA, nB, nC, D, cross2]
    ring
  have hxNum : nA*A.1+nB*B.1+nC*C.1=D*p.1 := by
    dsimp [nA, nB, nC, D, cross2]
    ring
  have hyNum : nA*A.2+nB*B.2+nC*C.2=D*p.2 := by
    dsimp [nA, nB, nC, D, cross2]
    ring
  let α := nA/D
  let β := nB/D
  let γ := nC/D
  have hα : 0 ≤ α := div_nonneg hnA hD.le
  have hβ : 0 ≤ β := div_nonneg hnB hD.le
  have hγ : 0 ≤ γ := div_nonneg hnC hD.le
  have hsum : α+β+γ=1 := by
    calc
      α+β+γ = (nA+nB+nC)/D := by dsimp [α, β, γ]; ring
      _ = D/D := by rw [hsumNum]
      _ = 1 := div_self hDne
  have hpoint : α • A + β • B + γ • C = p := by
    apply Prod.ext
    · change α*A.1+β*B.1+γ*C.1=p.1
      calc
        α*A.1+β*B.1+γ*C.1 = (nA*A.1+nB*B.1+nC*C.1)/D := by
          dsimp [α, β, γ]; ring
        _ = (D*p.1)/D := by rw [hxNum]
        _ = p.1 := by field_simp [hDne]
    · change α*A.2+β*B.2+γ*C.2=p.2
      calc
        α*A.2+β*B.2+γ*C.2 = (nA*A.2+nB*B.2+nC*C.2)/D := by
          dsimp [α, β, γ]; ring
        _ = (D*p.2)/D := by rw [hyNum]
        _ = p.2 := by field_simp [hDne]
  exact rationalHull_of_barycentric3 ha hb hc α β γ hα hβ hγ hsum hpoint

/-- One actual terminal collision triangle, derived from its three closed
integer halfplanes and the exact archived rational vertices. -/
theorem terminal1Triangle0_hull :
    terminal1Triangle0.carrier ⊆ rationalHull terminal1Triangle0Vertices := by
  intro p hp
  let a : QPoint := terminal1Triangle0Vertices[0]!
  let b : QPoint := terminal1Triangle0Vertices[1]!
  let c : QPoint := terminal1Triangle0Vertices[2]!
  have ha : a ∈ terminal1Triangle0Vertices := by simp [a, terminal1Triangle0Vertices]
  have hb : b ∈ terminal1Triangle0Vertices := by simp [b, terminal1Triangle0Vertices]
  have hc : c ∈ terminal1Triangle0Vertices := by simp [c, terminal1Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal1Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal1Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal1Triangle0])
  have hs1 : (terminal1Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal1Triangle0])
  have hs2 : (terminal1Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal1Triangle0])
  norm_num [terminal1Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal1Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal1Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal1Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
