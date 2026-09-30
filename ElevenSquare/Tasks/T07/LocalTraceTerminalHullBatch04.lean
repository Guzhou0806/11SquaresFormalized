import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch04
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal220_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal220Triangle0.carrier) : p ∈ rationalHull terminal220Triangle0Vertices := by
  let a : QPoint := terminal220Triangle0Vertices[0]!
  let b : QPoint := terminal220Triangle0Vertices[1]!
  let c : QPoint := terminal220Triangle0Vertices[2]!
  have ha : a ∈ terminal220Triangle0Vertices := by simp [a, terminal220Triangle0Vertices]
  have hb : b ∈ terminal220Triangle0Vertices := by simp [b, terminal220Triangle0Vertices]
  have hc : c ∈ terminal220Triangle0Vertices := by simp [c, terminal220Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal220Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal220Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal220Triangle0])
  have hs1 : (terminal220Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal220Triangle0])
  have hs2 : (terminal220Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal220Triangle0])
  norm_num [terminal220Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal220Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal220Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal220Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal221_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal221Triangle0.carrier) : p ∈ rationalHull terminal221Triangle0Vertices := by
  let a : QPoint := terminal221Triangle0Vertices[0]!
  let b : QPoint := terminal221Triangle0Vertices[1]!
  let c : QPoint := terminal221Triangle0Vertices[2]!
  have ha : a ∈ terminal221Triangle0Vertices := by simp [a, terminal221Triangle0Vertices]
  have hb : b ∈ terminal221Triangle0Vertices := by simp [b, terminal221Triangle0Vertices]
  have hc : c ∈ terminal221Triangle0Vertices := by simp [c, terminal221Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal221Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal221Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal221Triangle0])
  have hs1 : (terminal221Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal221Triangle0])
  have hs2 : (terminal221Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal221Triangle0])
  norm_num [terminal221Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal221Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal221Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal221Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal222_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal222Triangle0.carrier) : p ∈ rationalHull terminal222Triangle0Vertices := by
  let a : QPoint := terminal222Triangle0Vertices[0]!
  let b : QPoint := terminal222Triangle0Vertices[1]!
  let c : QPoint := terminal222Triangle0Vertices[2]!
  have ha : a ∈ terminal222Triangle0Vertices := by simp [a, terminal222Triangle0Vertices]
  have hb : b ∈ terminal222Triangle0Vertices := by simp [b, terminal222Triangle0Vertices]
  have hc : c ∈ terminal222Triangle0Vertices := by simp [c, terminal222Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal222Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal222Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal222Triangle0])
  have hs1 : (terminal222Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal222Triangle0])
  have hs2 : (terminal222Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal222Triangle0])
  norm_num [terminal222Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal222Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal222Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal222Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal223_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal223Triangle0.carrier) : p ∈ rationalHull terminal223Triangle0Vertices := by
  let a : QPoint := terminal223Triangle0Vertices[0]!
  let b : QPoint := terminal223Triangle0Vertices[1]!
  let c : QPoint := terminal223Triangle0Vertices[2]!
  have ha : a ∈ terminal223Triangle0Vertices := by simp [a, terminal223Triangle0Vertices]
  have hb : b ∈ terminal223Triangle0Vertices := by simp [b, terminal223Triangle0Vertices]
  have hc : c ∈ terminal223Triangle0Vertices := by simp [c, terminal223Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal223Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal223Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal223Triangle0])
  have hs1 : (terminal223Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal223Triangle0])
  have hs2 : (terminal223Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal223Triangle0])
  norm_num [terminal223Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal223Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal223Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal223Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal224_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal224Triangle0.carrier) : p ∈ rationalHull terminal224Triangle0Vertices := by
  let a : QPoint := terminal224Triangle0Vertices[0]!
  let b : QPoint := terminal224Triangle0Vertices[1]!
  let c : QPoint := terminal224Triangle0Vertices[2]!
  have ha : a ∈ terminal224Triangle0Vertices := by simp [a, terminal224Triangle0Vertices]
  have hb : b ∈ terminal224Triangle0Vertices := by simp [b, terminal224Triangle0Vertices]
  have hc : c ∈ terminal224Triangle0Vertices := by simp [c, terminal224Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal224Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal224Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal224Triangle0])
  have hs1 : (terminal224Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal224Triangle0])
  have hs2 : (terminal224Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal224Triangle0])
  norm_num [terminal224Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal224Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal224Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal224Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal225_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal225Triangle0.carrier) : p ∈ rationalHull terminal225Triangle0Vertices := by
  let a : QPoint := terminal225Triangle0Vertices[0]!
  let b : QPoint := terminal225Triangle0Vertices[1]!
  let c : QPoint := terminal225Triangle0Vertices[2]!
  have ha : a ∈ terminal225Triangle0Vertices := by simp [a, terminal225Triangle0Vertices]
  have hb : b ∈ terminal225Triangle0Vertices := by simp [b, terminal225Triangle0Vertices]
  have hc : c ∈ terminal225Triangle0Vertices := by simp [c, terminal225Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal225Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal225Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal225Triangle0])
  have hs1 : (terminal225Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal225Triangle0])
  have hs2 : (terminal225Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal225Triangle0])
  norm_num [terminal225Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal225Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal225Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal225Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal226_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal226Triangle0.carrier) : p ∈ rationalHull terminal226Triangle0Vertices := by
  let a : QPoint := terminal226Triangle0Vertices[0]!
  let b : QPoint := terminal226Triangle0Vertices[1]!
  let c : QPoint := terminal226Triangle0Vertices[2]!
  have ha : a ∈ terminal226Triangle0Vertices := by simp [a, terminal226Triangle0Vertices]
  have hb : b ∈ terminal226Triangle0Vertices := by simp [b, terminal226Triangle0Vertices]
  have hc : c ∈ terminal226Triangle0Vertices := by simp [c, terminal226Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal226Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal226Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal226Triangle0])
  have hs1 : (terminal226Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal226Triangle0])
  have hs2 : (terminal226Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal226Triangle0])
  norm_num [terminal226Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal226Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal226Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal226Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal227_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal227Triangle0.carrier) : p ∈ rationalHull terminal227Triangle0Vertices := by
  let a : QPoint := terminal227Triangle0Vertices[0]!
  let b : QPoint := terminal227Triangle0Vertices[1]!
  let c : QPoint := terminal227Triangle0Vertices[2]!
  have ha : a ∈ terminal227Triangle0Vertices := by simp [a, terminal227Triangle0Vertices]
  have hb : b ∈ terminal227Triangle0Vertices := by simp [b, terminal227Triangle0Vertices]
  have hc : c ∈ terminal227Triangle0Vertices := by simp [c, terminal227Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal227Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal227Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal227Triangle0])
  have hs1 : (terminal227Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal227Triangle0])
  have hs2 : (terminal227Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal227Triangle0])
  norm_num [terminal227Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal227Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal227Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal227Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal228_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal228Triangle0.carrier) : p ∈ rationalHull terminal228Triangle0Vertices := by
  let a : QPoint := terminal228Triangle0Vertices[0]!
  let b : QPoint := terminal228Triangle0Vertices[1]!
  let c : QPoint := terminal228Triangle0Vertices[2]!
  have ha : a ∈ terminal228Triangle0Vertices := by simp [a, terminal228Triangle0Vertices]
  have hb : b ∈ terminal228Triangle0Vertices := by simp [b, terminal228Triangle0Vertices]
  have hc : c ∈ terminal228Triangle0Vertices := by simp [c, terminal228Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal228Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal228Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal228Triangle0])
  have hs1 : (terminal228Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal228Triangle0])
  have hs2 : (terminal228Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal228Triangle0])
  norm_num [terminal228Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal228Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal228Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal228Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal229_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal229Triangle0.carrier) : p ∈ rationalHull terminal229Triangle0Vertices := by
  let a : QPoint := terminal229Triangle0Vertices[0]!
  let b : QPoint := terminal229Triangle0Vertices[1]!
  let c : QPoint := terminal229Triangle0Vertices[2]!
  have ha : a ∈ terminal229Triangle0Vertices := by simp [a, terminal229Triangle0Vertices]
  have hb : b ∈ terminal229Triangle0Vertices := by simp [b, terminal229Triangle0Vertices]
  have hc : c ∈ terminal229Triangle0Vertices := by simp [c, terminal229Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal229Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal229Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal229Triangle0])
  have hs1 : (terminal229Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal229Triangle0])
  have hs2 : (terminal229Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal229Triangle0])
  norm_num [terminal229Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal229Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal229Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal229Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
