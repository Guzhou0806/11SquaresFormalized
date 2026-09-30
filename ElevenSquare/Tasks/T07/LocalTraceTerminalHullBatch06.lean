import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch06
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal240_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal240Triangle0.carrier) : p ∈ rationalHull terminal240Triangle0Vertices := by
  let a : QPoint := terminal240Triangle0Vertices[0]!
  let b : QPoint := terminal240Triangle0Vertices[1]!
  let c : QPoint := terminal240Triangle0Vertices[2]!
  have ha : a ∈ terminal240Triangle0Vertices := by simp [a, terminal240Triangle0Vertices]
  have hb : b ∈ terminal240Triangle0Vertices := by simp [b, terminal240Triangle0Vertices]
  have hc : c ∈ terminal240Triangle0Vertices := by simp [c, terminal240Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal240Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal240Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal240Triangle0])
  have hs1 : (terminal240Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal240Triangle0])
  have hs2 : (terminal240Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal240Triangle0])
  norm_num [terminal240Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal240Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal240Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal240Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal241_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal241Triangle0.carrier) : p ∈ rationalHull terminal241Triangle0Vertices := by
  let a : QPoint := terminal241Triangle0Vertices[0]!
  let b : QPoint := terminal241Triangle0Vertices[1]!
  let c : QPoint := terminal241Triangle0Vertices[2]!
  have ha : a ∈ terminal241Triangle0Vertices := by simp [a, terminal241Triangle0Vertices]
  have hb : b ∈ terminal241Triangle0Vertices := by simp [b, terminal241Triangle0Vertices]
  have hc : c ∈ terminal241Triangle0Vertices := by simp [c, terminal241Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal241Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal241Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal241Triangle0])
  have hs1 : (terminal241Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal241Triangle0])
  have hs2 : (terminal241Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal241Triangle0])
  norm_num [terminal241Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal241Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal241Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal241Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal242_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal242Triangle0.carrier) : p ∈ rationalHull terminal242Triangle0Vertices := by
  let a : QPoint := terminal242Triangle0Vertices[0]!
  let b : QPoint := terminal242Triangle0Vertices[1]!
  let c : QPoint := terminal242Triangle0Vertices[2]!
  have ha : a ∈ terminal242Triangle0Vertices := by simp [a, terminal242Triangle0Vertices]
  have hb : b ∈ terminal242Triangle0Vertices := by simp [b, terminal242Triangle0Vertices]
  have hc : c ∈ terminal242Triangle0Vertices := by simp [c, terminal242Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal242Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal242Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal242Triangle0])
  have hs1 : (terminal242Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal242Triangle0])
  have hs2 : (terminal242Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal242Triangle0])
  norm_num [terminal242Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal242Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal242Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal242Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal242_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal242Triangle1.carrier) : p ∈ rationalHull terminal242Triangle1Vertices := by
  let a : QPoint := terminal242Triangle1Vertices[0]!
  let b : QPoint := terminal242Triangle1Vertices[1]!
  let c : QPoint := terminal242Triangle1Vertices[2]!
  have ha : a ∈ terminal242Triangle1Vertices := by simp [a, terminal242Triangle1Vertices]
  have hb : b ∈ terminal242Triangle1Vertices := by simp [b, terminal242Triangle1Vertices]
  have hc : c ∈ terminal242Triangle1Vertices := by simp [c, terminal242Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal242Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal242Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal242Triangle1])
  have hs1 : (terminal242Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal242Triangle1])
  have hs2 : (terminal242Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal242Triangle1])
  norm_num [terminal242Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal242Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal242Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal242Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal243_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal243Triangle0.carrier) : p ∈ rationalHull terminal243Triangle0Vertices := by
  let a : QPoint := terminal243Triangle0Vertices[0]!
  let b : QPoint := terminal243Triangle0Vertices[1]!
  let c : QPoint := terminal243Triangle0Vertices[2]!
  have ha : a ∈ terminal243Triangle0Vertices := by simp [a, terminal243Triangle0Vertices]
  have hb : b ∈ terminal243Triangle0Vertices := by simp [b, terminal243Triangle0Vertices]
  have hc : c ∈ terminal243Triangle0Vertices := by simp [c, terminal243Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal243Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal243Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal243Triangle0])
  have hs1 : (terminal243Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal243Triangle0])
  have hs2 : (terminal243Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal243Triangle0])
  norm_num [terminal243Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal243Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal243Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal243Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal243_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal243Triangle1.carrier) : p ∈ rationalHull terminal243Triangle1Vertices := by
  let a : QPoint := terminal243Triangle1Vertices[0]!
  let b : QPoint := terminal243Triangle1Vertices[1]!
  let c : QPoint := terminal243Triangle1Vertices[2]!
  have ha : a ∈ terminal243Triangle1Vertices := by simp [a, terminal243Triangle1Vertices]
  have hb : b ∈ terminal243Triangle1Vertices := by simp [b, terminal243Triangle1Vertices]
  have hc : c ∈ terminal243Triangle1Vertices := by simp [c, terminal243Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal243Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal243Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal243Triangle1])
  have hs1 : (terminal243Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal243Triangle1])
  have hs2 : (terminal243Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal243Triangle1])
  norm_num [terminal243Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal243Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal243Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal243Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal244_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal244Triangle0.carrier) : p ∈ rationalHull terminal244Triangle0Vertices := by
  let a : QPoint := terminal244Triangle0Vertices[0]!
  let b : QPoint := terminal244Triangle0Vertices[1]!
  let c : QPoint := terminal244Triangle0Vertices[2]!
  have ha : a ∈ terminal244Triangle0Vertices := by simp [a, terminal244Triangle0Vertices]
  have hb : b ∈ terminal244Triangle0Vertices := by simp [b, terminal244Triangle0Vertices]
  have hc : c ∈ terminal244Triangle0Vertices := by simp [c, terminal244Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal244Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal244Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal244Triangle0])
  have hs1 : (terminal244Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal244Triangle0])
  have hs2 : (terminal244Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal244Triangle0])
  norm_num [terminal244Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal244Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal244Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal244Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal244_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal244Triangle1.carrier) : p ∈ rationalHull terminal244Triangle1Vertices := by
  let a : QPoint := terminal244Triangle1Vertices[0]!
  let b : QPoint := terminal244Triangle1Vertices[1]!
  let c : QPoint := terminal244Triangle1Vertices[2]!
  have ha : a ∈ terminal244Triangle1Vertices := by simp [a, terminal244Triangle1Vertices]
  have hb : b ∈ terminal244Triangle1Vertices := by simp [b, terminal244Triangle1Vertices]
  have hc : c ∈ terminal244Triangle1Vertices := by simp [c, terminal244Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal244Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal244Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal244Triangle1])
  have hs1 : (terminal244Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal244Triangle1])
  have hs2 : (terminal244Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal244Triangle1])
  norm_num [terminal244Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal244Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal244Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal244Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal245_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal245Triangle0.carrier) : p ∈ rationalHull terminal245Triangle0Vertices := by
  let a : QPoint := terminal245Triangle0Vertices[0]!
  let b : QPoint := terminal245Triangle0Vertices[1]!
  let c : QPoint := terminal245Triangle0Vertices[2]!
  have ha : a ∈ terminal245Triangle0Vertices := by simp [a, terminal245Triangle0Vertices]
  have hb : b ∈ terminal245Triangle0Vertices := by simp [b, terminal245Triangle0Vertices]
  have hc : c ∈ terminal245Triangle0Vertices := by simp [c, terminal245Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal245Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal245Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal245Triangle0])
  have hs1 : (terminal245Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal245Triangle0])
  have hs2 : (terminal245Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal245Triangle0])
  norm_num [terminal245Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal245Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal245Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal245Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal245_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal245Triangle1.carrier) : p ∈ rationalHull terminal245Triangle1Vertices := by
  let a : QPoint := terminal245Triangle1Vertices[0]!
  let b : QPoint := terminal245Triangle1Vertices[1]!
  let c : QPoint := terminal245Triangle1Vertices[2]!
  have ha : a ∈ terminal245Triangle1Vertices := by simp [a, terminal245Triangle1Vertices]
  have hb : b ∈ terminal245Triangle1Vertices := by simp [b, terminal245Triangle1Vertices]
  have hc : c ∈ terminal245Triangle1Vertices := by simp [c, terminal245Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal245Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal245Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal245Triangle1])
  have hs1 : (terminal245Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal245Triangle1])
  have hs2 : (terminal245Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal245Triangle1])
  norm_num [terminal245Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal245Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal245Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal245Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal246_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal246Triangle0.carrier) : p ∈ rationalHull terminal246Triangle0Vertices := by
  let a : QPoint := terminal246Triangle0Vertices[0]!
  let b : QPoint := terminal246Triangle0Vertices[1]!
  let c : QPoint := terminal246Triangle0Vertices[2]!
  have ha : a ∈ terminal246Triangle0Vertices := by simp [a, terminal246Triangle0Vertices]
  have hb : b ∈ terminal246Triangle0Vertices := by simp [b, terminal246Triangle0Vertices]
  have hc : c ∈ terminal246Triangle0Vertices := by simp [c, terminal246Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal246Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal246Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal246Triangle0])
  have hs1 : (terminal246Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal246Triangle0])
  have hs2 : (terminal246Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal246Triangle0])
  norm_num [terminal246Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal246Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal246Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal246Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal246_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal246Triangle1.carrier) : p ∈ rationalHull terminal246Triangle1Vertices := by
  let a : QPoint := terminal246Triangle1Vertices[0]!
  let b : QPoint := terminal246Triangle1Vertices[1]!
  let c : QPoint := terminal246Triangle1Vertices[2]!
  have ha : a ∈ terminal246Triangle1Vertices := by simp [a, terminal246Triangle1Vertices]
  have hb : b ∈ terminal246Triangle1Vertices := by simp [b, terminal246Triangle1Vertices]
  have hc : c ∈ terminal246Triangle1Vertices := by simp [c, terminal246Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal246Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal246Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal246Triangle1])
  have hs1 : (terminal246Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal246Triangle1])
  have hs2 : (terminal246Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal246Triangle1])
  norm_num [terminal246Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal246Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal246Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal246Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal247_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal247Triangle0.carrier) : p ∈ rationalHull terminal247Triangle0Vertices := by
  let a : QPoint := terminal247Triangle0Vertices[0]!
  let b : QPoint := terminal247Triangle0Vertices[1]!
  let c : QPoint := terminal247Triangle0Vertices[2]!
  have ha : a ∈ terminal247Triangle0Vertices := by simp [a, terminal247Triangle0Vertices]
  have hb : b ∈ terminal247Triangle0Vertices := by simp [b, terminal247Triangle0Vertices]
  have hc : c ∈ terminal247Triangle0Vertices := by simp [c, terminal247Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal247Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal247Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal247Triangle0])
  have hs1 : (terminal247Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal247Triangle0])
  have hs2 : (terminal247Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal247Triangle0])
  norm_num [terminal247Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal247Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal247Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal247Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal247_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal247Triangle1.carrier) : p ∈ rationalHull terminal247Triangle1Vertices := by
  let a : QPoint := terminal247Triangle1Vertices[0]!
  let b : QPoint := terminal247Triangle1Vertices[1]!
  let c : QPoint := terminal247Triangle1Vertices[2]!
  have ha : a ∈ terminal247Triangle1Vertices := by simp [a, terminal247Triangle1Vertices]
  have hb : b ∈ terminal247Triangle1Vertices := by simp [b, terminal247Triangle1Vertices]
  have hc : c ∈ terminal247Triangle1Vertices := by simp [c, terminal247Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal247Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal247Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal247Triangle1])
  have hs1 : (terminal247Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal247Triangle1])
  have hs2 : (terminal247Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal247Triangle1])
  norm_num [terminal247Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal247Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal247Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal247Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal248_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal248Triangle0.carrier) : p ∈ rationalHull terminal248Triangle0Vertices := by
  let a : QPoint := terminal248Triangle0Vertices[0]!
  let b : QPoint := terminal248Triangle0Vertices[1]!
  let c : QPoint := terminal248Triangle0Vertices[2]!
  have ha : a ∈ terminal248Triangle0Vertices := by simp [a, terminal248Triangle0Vertices]
  have hb : b ∈ terminal248Triangle0Vertices := by simp [b, terminal248Triangle0Vertices]
  have hc : c ∈ terminal248Triangle0Vertices := by simp [c, terminal248Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal248Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal248Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal248Triangle0])
  have hs1 : (terminal248Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal248Triangle0])
  have hs2 : (terminal248Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal248Triangle0])
  norm_num [terminal248Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal248Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal248Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal248Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal248_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal248Triangle1.carrier) : p ∈ rationalHull terminal248Triangle1Vertices := by
  let a : QPoint := terminal248Triangle1Vertices[0]!
  let b : QPoint := terminal248Triangle1Vertices[1]!
  let c : QPoint := terminal248Triangle1Vertices[2]!
  have ha : a ∈ terminal248Triangle1Vertices := by simp [a, terminal248Triangle1Vertices]
  have hb : b ∈ terminal248Triangle1Vertices := by simp [b, terminal248Triangle1Vertices]
  have hc : c ∈ terminal248Triangle1Vertices := by simp [c, terminal248Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal248Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal248Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal248Triangle1])
  have hs1 : (terminal248Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal248Triangle1])
  have hs2 : (terminal248Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal248Triangle1])
  norm_num [terminal248Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal248Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal248Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal248Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal249_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal249Triangle0.carrier) : p ∈ rationalHull terminal249Triangle0Vertices := by
  let a : QPoint := terminal249Triangle0Vertices[0]!
  let b : QPoint := terminal249Triangle0Vertices[1]!
  let c : QPoint := terminal249Triangle0Vertices[2]!
  have ha : a ∈ terminal249Triangle0Vertices := by simp [a, terminal249Triangle0Vertices]
  have hb : b ∈ terminal249Triangle0Vertices := by simp [b, terminal249Triangle0Vertices]
  have hc : c ∈ terminal249Triangle0Vertices := by simp [c, terminal249Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal249Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal249Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal249Triangle0])
  have hs1 : (terminal249Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal249Triangle0])
  have hs2 : (terminal249Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal249Triangle0])
  norm_num [terminal249Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal249Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal249Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal249Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal249_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal249Triangle1.carrier) : p ∈ rationalHull terminal249Triangle1Vertices := by
  let a : QPoint := terminal249Triangle1Vertices[0]!
  let b : QPoint := terminal249Triangle1Vertices[1]!
  let c : QPoint := terminal249Triangle1Vertices[2]!
  have ha : a ∈ terminal249Triangle1Vertices := by simp [a, terminal249Triangle1Vertices]
  have hb : b ∈ terminal249Triangle1Vertices := by simp [b, terminal249Triangle1Vertices]
  have hc : c ∈ terminal249Triangle1Vertices := by simp [c, terminal249Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal249Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal249Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal249Triangle1])
  have hs1 : (terminal249Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal249Triangle1])
  have hs2 : (terminal249Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal249Triangle1])
  norm_num [terminal249Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal249Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal249Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal249Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
