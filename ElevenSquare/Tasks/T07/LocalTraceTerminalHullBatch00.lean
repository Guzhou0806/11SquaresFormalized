import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch00
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal0_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal0Triangle0.carrier) : p ∈ rationalHull terminal0Triangle0Vertices := by
  let a : QPoint := terminal0Triangle0Vertices[0]!
  let b : QPoint := terminal0Triangle0Vertices[1]!
  let c : QPoint := terminal0Triangle0Vertices[2]!
  have ha : a ∈ terminal0Triangle0Vertices := by simp [a, terminal0Triangle0Vertices]
  have hb : b ∈ terminal0Triangle0Vertices := by simp [b, terminal0Triangle0Vertices]
  have hc : c ∈ terminal0Triangle0Vertices := by simp [c, terminal0Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal0Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal0Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal0Triangle0])
  have hs1 : (terminal0Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal0Triangle0])
  have hs2 : (terminal0Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal0Triangle0])
  norm_num [terminal0Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal0Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal0Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal0Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal0_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal0Triangle1.carrier) : p ∈ rationalHull terminal0Triangle1Vertices := by
  let a : QPoint := terminal0Triangle1Vertices[0]!
  let b : QPoint := terminal0Triangle1Vertices[1]!
  let c : QPoint := terminal0Triangle1Vertices[2]!
  have ha : a ∈ terminal0Triangle1Vertices := by simp [a, terminal0Triangle1Vertices]
  have hb : b ∈ terminal0Triangle1Vertices := by simp [b, terminal0Triangle1Vertices]
  have hc : c ∈ terminal0Triangle1Vertices := by simp [c, terminal0Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal0Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal0Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal0Triangle1])
  have hs1 : (terminal0Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal0Triangle1])
  have hs2 : (terminal0Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal0Triangle1])
  norm_num [terminal0Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal0Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal0Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal0Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal1_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal1Triangle0.carrier) : p ∈ rationalHull terminal1Triangle0Vertices := by
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

theorem terminal1_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal1Triangle1.carrier) : p ∈ rationalHull terminal1Triangle1Vertices := by
  let a : QPoint := terminal1Triangle1Vertices[0]!
  let b : QPoint := terminal1Triangle1Vertices[1]!
  let c : QPoint := terminal1Triangle1Vertices[2]!
  have ha : a ∈ terminal1Triangle1Vertices := by simp [a, terminal1Triangle1Vertices]
  have hb : b ∈ terminal1Triangle1Vertices := by simp [b, terminal1Triangle1Vertices]
  have hc : c ∈ terminal1Triangle1Vertices := by simp [c, terminal1Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal1Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal1Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal1Triangle1])
  have hs1 : (terminal1Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal1Triangle1])
  have hs2 : (terminal1Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal1Triangle1])
  norm_num [terminal1Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal1Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal1Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal1Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal2_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal2Triangle0.carrier) : p ∈ rationalHull terminal2Triangle0Vertices := by
  let a : QPoint := terminal2Triangle0Vertices[0]!
  let b : QPoint := terminal2Triangle0Vertices[1]!
  let c : QPoint := terminal2Triangle0Vertices[2]!
  have ha : a ∈ terminal2Triangle0Vertices := by simp [a, terminal2Triangle0Vertices]
  have hb : b ∈ terminal2Triangle0Vertices := by simp [b, terminal2Triangle0Vertices]
  have hc : c ∈ terminal2Triangle0Vertices := by simp [c, terminal2Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal2Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal2Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal2Triangle0])
  have hs1 : (terminal2Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal2Triangle0])
  have hs2 : (terminal2Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal2Triangle0])
  norm_num [terminal2Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal2Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal2Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal2Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal2_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal2Triangle1.carrier) : p ∈ rationalHull terminal2Triangle1Vertices := by
  let a : QPoint := terminal2Triangle1Vertices[0]!
  let b : QPoint := terminal2Triangle1Vertices[1]!
  let c : QPoint := terminal2Triangle1Vertices[2]!
  have ha : a ∈ terminal2Triangle1Vertices := by simp [a, terminal2Triangle1Vertices]
  have hb : b ∈ terminal2Triangle1Vertices := by simp [b, terminal2Triangle1Vertices]
  have hc : c ∈ terminal2Triangle1Vertices := by simp [c, terminal2Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal2Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal2Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal2Triangle1])
  have hs1 : (terminal2Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal2Triangle1])
  have hs2 : (terminal2Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal2Triangle1])
  norm_num [terminal2Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal2Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal2Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal2Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal3_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal3Triangle0.carrier) : p ∈ rationalHull terminal3Triangle0Vertices := by
  let a : QPoint := terminal3Triangle0Vertices[0]!
  let b : QPoint := terminal3Triangle0Vertices[1]!
  let c : QPoint := terminal3Triangle0Vertices[2]!
  have ha : a ∈ terminal3Triangle0Vertices := by simp [a, terminal3Triangle0Vertices]
  have hb : b ∈ terminal3Triangle0Vertices := by simp [b, terminal3Triangle0Vertices]
  have hc : c ∈ terminal3Triangle0Vertices := by simp [c, terminal3Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal3Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal3Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal3Triangle0])
  have hs1 : (terminal3Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal3Triangle0])
  have hs2 : (terminal3Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal3Triangle0])
  norm_num [terminal3Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal3Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal3Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal3Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal3_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal3Triangle1.carrier) : p ∈ rationalHull terminal3Triangle1Vertices := by
  let a : QPoint := terminal3Triangle1Vertices[0]!
  let b : QPoint := terminal3Triangle1Vertices[1]!
  let c : QPoint := terminal3Triangle1Vertices[2]!
  have ha : a ∈ terminal3Triangle1Vertices := by simp [a, terminal3Triangle1Vertices]
  have hb : b ∈ terminal3Triangle1Vertices := by simp [b, terminal3Triangle1Vertices]
  have hc : c ∈ terminal3Triangle1Vertices := by simp [c, terminal3Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal3Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal3Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal3Triangle1])
  have hs1 : (terminal3Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal3Triangle1])
  have hs2 : (terminal3Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal3Triangle1])
  norm_num [terminal3Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal3Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal3Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal3Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal4_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal4Triangle0.carrier) : p ∈ rationalHull terminal4Triangle0Vertices := by
  let a : QPoint := terminal4Triangle0Vertices[0]!
  let b : QPoint := terminal4Triangle0Vertices[1]!
  let c : QPoint := terminal4Triangle0Vertices[2]!
  have ha : a ∈ terminal4Triangle0Vertices := by simp [a, terminal4Triangle0Vertices]
  have hb : b ∈ terminal4Triangle0Vertices := by simp [b, terminal4Triangle0Vertices]
  have hc : c ∈ terminal4Triangle0Vertices := by simp [c, terminal4Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal4Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal4Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal4Triangle0])
  have hs1 : (terminal4Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal4Triangle0])
  have hs2 : (terminal4Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal4Triangle0])
  norm_num [terminal4Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal4Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal4Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal4Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal4_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal4Triangle1.carrier) : p ∈ rationalHull terminal4Triangle1Vertices := by
  let a : QPoint := terminal4Triangle1Vertices[0]!
  let b : QPoint := terminal4Triangle1Vertices[1]!
  let c : QPoint := terminal4Triangle1Vertices[2]!
  have ha : a ∈ terminal4Triangle1Vertices := by simp [a, terminal4Triangle1Vertices]
  have hb : b ∈ terminal4Triangle1Vertices := by simp [b, terminal4Triangle1Vertices]
  have hc : c ∈ terminal4Triangle1Vertices := by simp [c, terminal4Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal4Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal4Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal4Triangle1])
  have hs1 : (terminal4Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal4Triangle1])
  have hs2 : (terminal4Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal4Triangle1])
  norm_num [terminal4Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal4Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal4Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal4Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal5_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal5Triangle0.carrier) : p ∈ rationalHull terminal5Triangle0Vertices := by
  let a : QPoint := terminal5Triangle0Vertices[0]!
  let b : QPoint := terminal5Triangle0Vertices[1]!
  let c : QPoint := terminal5Triangle0Vertices[2]!
  have ha : a ∈ terminal5Triangle0Vertices := by simp [a, terminal5Triangle0Vertices]
  have hb : b ∈ terminal5Triangle0Vertices := by simp [b, terminal5Triangle0Vertices]
  have hc : c ∈ terminal5Triangle0Vertices := by simp [c, terminal5Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal5Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal5Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal5Triangle0])
  have hs1 : (terminal5Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal5Triangle0])
  have hs2 : (terminal5Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal5Triangle0])
  norm_num [terminal5Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal5Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal5Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal5Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal5_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal5Triangle1.carrier) : p ∈ rationalHull terminal5Triangle1Vertices := by
  let a : QPoint := terminal5Triangle1Vertices[0]!
  let b : QPoint := terminal5Triangle1Vertices[1]!
  let c : QPoint := terminal5Triangle1Vertices[2]!
  have ha : a ∈ terminal5Triangle1Vertices := by simp [a, terminal5Triangle1Vertices]
  have hb : b ∈ terminal5Triangle1Vertices := by simp [b, terminal5Triangle1Vertices]
  have hc : c ∈ terminal5Triangle1Vertices := by simp [c, terminal5Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal5Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal5Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal5Triangle1])
  have hs1 : (terminal5Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal5Triangle1])
  have hs2 : (terminal5Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal5Triangle1])
  norm_num [terminal5Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal5Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal5Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal5Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal6_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal6Triangle0.carrier) : p ∈ rationalHull terminal6Triangle0Vertices := by
  let a : QPoint := terminal6Triangle0Vertices[0]!
  let b : QPoint := terminal6Triangle0Vertices[1]!
  let c : QPoint := terminal6Triangle0Vertices[2]!
  have ha : a ∈ terminal6Triangle0Vertices := by simp [a, terminal6Triangle0Vertices]
  have hb : b ∈ terminal6Triangle0Vertices := by simp [b, terminal6Triangle0Vertices]
  have hc : c ∈ terminal6Triangle0Vertices := by simp [c, terminal6Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal6Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal6Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal6Triangle0])
  have hs1 : (terminal6Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal6Triangle0])
  have hs2 : (terminal6Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal6Triangle0])
  norm_num [terminal6Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal6Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal6Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal6Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal6_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal6Triangle1.carrier) : p ∈ rationalHull terminal6Triangle1Vertices := by
  let a : QPoint := terminal6Triangle1Vertices[0]!
  let b : QPoint := terminal6Triangle1Vertices[1]!
  let c : QPoint := terminal6Triangle1Vertices[2]!
  have ha : a ∈ terminal6Triangle1Vertices := by simp [a, terminal6Triangle1Vertices]
  have hb : b ∈ terminal6Triangle1Vertices := by simp [b, terminal6Triangle1Vertices]
  have hc : c ∈ terminal6Triangle1Vertices := by simp [c, terminal6Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal6Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal6Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal6Triangle1])
  have hs1 : (terminal6Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal6Triangle1])
  have hs2 : (terminal6Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal6Triangle1])
  norm_num [terminal6Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal6Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal6Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal6Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal7_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal7Triangle0.carrier) : p ∈ rationalHull terminal7Triangle0Vertices := by
  let a : QPoint := terminal7Triangle0Vertices[0]!
  let b : QPoint := terminal7Triangle0Vertices[1]!
  let c : QPoint := terminal7Triangle0Vertices[2]!
  have ha : a ∈ terminal7Triangle0Vertices := by simp [a, terminal7Triangle0Vertices]
  have hb : b ∈ terminal7Triangle0Vertices := by simp [b, terminal7Triangle0Vertices]
  have hc : c ∈ terminal7Triangle0Vertices := by simp [c, terminal7Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal7Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal7Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal7Triangle0])
  have hs1 : (terminal7Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal7Triangle0])
  have hs2 : (terminal7Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal7Triangle0])
  norm_num [terminal7Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal7Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal7Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal7Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal7_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal7Triangle1.carrier) : p ∈ rationalHull terminal7Triangle1Vertices := by
  let a : QPoint := terminal7Triangle1Vertices[0]!
  let b : QPoint := terminal7Triangle1Vertices[1]!
  let c : QPoint := terminal7Triangle1Vertices[2]!
  have ha : a ∈ terminal7Triangle1Vertices := by simp [a, terminal7Triangle1Vertices]
  have hb : b ∈ terminal7Triangle1Vertices := by simp [b, terminal7Triangle1Vertices]
  have hc : c ∈ terminal7Triangle1Vertices := by simp [c, terminal7Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal7Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal7Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal7Triangle1])
  have hs1 : (terminal7Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal7Triangle1])
  have hs2 : (terminal7Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal7Triangle1])
  norm_num [terminal7Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal7Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal7Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal7Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal8_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal8Triangle0.carrier) : p ∈ rationalHull terminal8Triangle0Vertices := by
  let a : QPoint := terminal8Triangle0Vertices[0]!
  let b : QPoint := terminal8Triangle0Vertices[1]!
  let c : QPoint := terminal8Triangle0Vertices[2]!
  have ha : a ∈ terminal8Triangle0Vertices := by simp [a, terminal8Triangle0Vertices]
  have hb : b ∈ terminal8Triangle0Vertices := by simp [b, terminal8Triangle0Vertices]
  have hc : c ∈ terminal8Triangle0Vertices := by simp [c, terminal8Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal8Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal8Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal8Triangle0])
  have hs1 : (terminal8Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal8Triangle0])
  have hs2 : (terminal8Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal8Triangle0])
  norm_num [terminal8Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal8Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal8Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal8Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal8_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal8Triangle1.carrier) : p ∈ rationalHull terminal8Triangle1Vertices := by
  let a : QPoint := terminal8Triangle1Vertices[0]!
  let b : QPoint := terminal8Triangle1Vertices[1]!
  let c : QPoint := terminal8Triangle1Vertices[2]!
  have ha : a ∈ terminal8Triangle1Vertices := by simp [a, terminal8Triangle1Vertices]
  have hb : b ∈ terminal8Triangle1Vertices := by simp [b, terminal8Triangle1Vertices]
  have hc : c ∈ terminal8Triangle1Vertices := by simp [c, terminal8Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal8Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal8Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal8Triangle1])
  have hs1 : (terminal8Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal8Triangle1])
  have hs2 : (terminal8Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal8Triangle1])
  norm_num [terminal8Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal8Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal8Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal8Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal9_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal9Triangle0.carrier) : p ∈ rationalHull terminal9Triangle0Vertices := by
  let a : QPoint := terminal9Triangle0Vertices[0]!
  let b : QPoint := terminal9Triangle0Vertices[1]!
  let c : QPoint := terminal9Triangle0Vertices[2]!
  have ha : a ∈ terminal9Triangle0Vertices := by simp [a, terminal9Triangle0Vertices]
  have hb : b ∈ terminal9Triangle0Vertices := by simp [b, terminal9Triangle0Vertices]
  have hc : c ∈ terminal9Triangle0Vertices := by simp [c, terminal9Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal9Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal9Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal9Triangle0])
  have hs1 : (terminal9Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal9Triangle0])
  have hs2 : (terminal9Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal9Triangle0])
  norm_num [terminal9Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal9Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal9Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal9Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal9_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal9Triangle1.carrier) : p ∈ rationalHull terminal9Triangle1Vertices := by
  let a : QPoint := terminal9Triangle1Vertices[0]!
  let b : QPoint := terminal9Triangle1Vertices[1]!
  let c : QPoint := terminal9Triangle1Vertices[2]!
  have ha : a ∈ terminal9Triangle1Vertices := by simp [a, terminal9Triangle1Vertices]
  have hb : b ∈ terminal9Triangle1Vertices := by simp [b, terminal9Triangle1Vertices]
  have hc : c ∈ terminal9Triangle1Vertices := by simp [c, terminal9Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal9Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal9Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal9Triangle1])
  have hs1 : (terminal9Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal9Triangle1])
  have hs2 : (terminal9Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal9Triangle1])
  norm_num [terminal9Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal9Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal9Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal9Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
