import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch02
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal21_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal21Triangle0.carrier) : p ∈ rationalHull terminal21Triangle0Vertices := by
  let a : QPoint := terminal21Triangle0Vertices[0]!
  let b : QPoint := terminal21Triangle0Vertices[1]!
  let c : QPoint := terminal21Triangle0Vertices[2]!
  have ha : a ∈ terminal21Triangle0Vertices := by simp [a, terminal21Triangle0Vertices]
  have hb : b ∈ terminal21Triangle0Vertices := by simp [b, terminal21Triangle0Vertices]
  have hc : c ∈ terminal21Triangle0Vertices := by simp [c, terminal21Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal21Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal21Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal21Triangle0])
  have hs1 : (terminal21Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal21Triangle0])
  have hs2 : (terminal21Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal21Triangle0])
  norm_num [terminal21Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal21Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal21Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal21Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
