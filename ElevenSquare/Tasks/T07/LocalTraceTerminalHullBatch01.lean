import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch01
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal10_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal10Triangle0.carrier) : p ∈ rationalHull terminal10Triangle0Vertices := by
  let a : QPoint := terminal10Triangle0Vertices[0]!
  let b : QPoint := terminal10Triangle0Vertices[1]!
  let c : QPoint := terminal10Triangle0Vertices[2]!
  have ha : a ∈ terminal10Triangle0Vertices := by simp [a, terminal10Triangle0Vertices]
  have hb : b ∈ terminal10Triangle0Vertices := by simp [b, terminal10Triangle0Vertices]
  have hc : c ∈ terminal10Triangle0Vertices := by simp [c, terminal10Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal10Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal10Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal10Triangle0])
  have hs1 : (terminal10Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal10Triangle0])
  have hs2 : (terminal10Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal10Triangle0])
  norm_num [terminal10Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal10Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal10Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal10Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal10_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal10Triangle1.carrier) : p ∈ rationalHull terminal10Triangle1Vertices := by
  let a : QPoint := terminal10Triangle1Vertices[0]!
  let b : QPoint := terminal10Triangle1Vertices[1]!
  let c : QPoint := terminal10Triangle1Vertices[2]!
  have ha : a ∈ terminal10Triangle1Vertices := by simp [a, terminal10Triangle1Vertices]
  have hb : b ∈ terminal10Triangle1Vertices := by simp [b, terminal10Triangle1Vertices]
  have hc : c ∈ terminal10Triangle1Vertices := by simp [c, terminal10Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal10Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal10Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal10Triangle1])
  have hs1 : (terminal10Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal10Triangle1])
  have hs2 : (terminal10Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal10Triangle1])
  norm_num [terminal10Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal10Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal10Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal10Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal11_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal11Triangle0.carrier) : p ∈ rationalHull terminal11Triangle0Vertices := by
  let a : QPoint := terminal11Triangle0Vertices[0]!
  let b : QPoint := terminal11Triangle0Vertices[1]!
  let c : QPoint := terminal11Triangle0Vertices[2]!
  have ha : a ∈ terminal11Triangle0Vertices := by simp [a, terminal11Triangle0Vertices]
  have hb : b ∈ terminal11Triangle0Vertices := by simp [b, terminal11Triangle0Vertices]
  have hc : c ∈ terminal11Triangle0Vertices := by simp [c, terminal11Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal11Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal11Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal11Triangle0])
  have hs1 : (terminal11Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal11Triangle0])
  have hs2 : (terminal11Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal11Triangle0])
  norm_num [terminal11Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal11Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal11Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal11Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal11_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal11Triangle1.carrier) : p ∈ rationalHull terminal11Triangle1Vertices := by
  let a : QPoint := terminal11Triangle1Vertices[0]!
  let b : QPoint := terminal11Triangle1Vertices[1]!
  let c : QPoint := terminal11Triangle1Vertices[2]!
  have ha : a ∈ terminal11Triangle1Vertices := by simp [a, terminal11Triangle1Vertices]
  have hb : b ∈ terminal11Triangle1Vertices := by simp [b, terminal11Triangle1Vertices]
  have hc : c ∈ terminal11Triangle1Vertices := by simp [c, terminal11Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal11Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal11Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal11Triangle1])
  have hs1 : (terminal11Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal11Triangle1])
  have hs2 : (terminal11Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal11Triangle1])
  norm_num [terminal11Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal11Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal11Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal11Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal12_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal12Triangle0.carrier) : p ∈ rationalHull terminal12Triangle0Vertices := by
  let a : QPoint := terminal12Triangle0Vertices[0]!
  let b : QPoint := terminal12Triangle0Vertices[1]!
  let c : QPoint := terminal12Triangle0Vertices[2]!
  have ha : a ∈ terminal12Triangle0Vertices := by simp [a, terminal12Triangle0Vertices]
  have hb : b ∈ terminal12Triangle0Vertices := by simp [b, terminal12Triangle0Vertices]
  have hc : c ∈ terminal12Triangle0Vertices := by simp [c, terminal12Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal12Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal12Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal12Triangle0])
  have hs1 : (terminal12Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal12Triangle0])
  have hs2 : (terminal12Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal12Triangle0])
  norm_num [terminal12Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal12Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal12Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal12Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal12_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal12Triangle1.carrier) : p ∈ rationalHull terminal12Triangle1Vertices := by
  let a : QPoint := terminal12Triangle1Vertices[0]!
  let b : QPoint := terminal12Triangle1Vertices[1]!
  let c : QPoint := terminal12Triangle1Vertices[2]!
  have ha : a ∈ terminal12Triangle1Vertices := by simp [a, terminal12Triangle1Vertices]
  have hb : b ∈ terminal12Triangle1Vertices := by simp [b, terminal12Triangle1Vertices]
  have hc : c ∈ terminal12Triangle1Vertices := by simp [c, terminal12Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal12Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal12Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal12Triangle1])
  have hs1 : (terminal12Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal12Triangle1])
  have hs2 : (terminal12Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal12Triangle1])
  norm_num [terminal12Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal12Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal12Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal12Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal13_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal13Triangle0.carrier) : p ∈ rationalHull terminal13Triangle0Vertices := by
  let a : QPoint := terminal13Triangle0Vertices[0]!
  let b : QPoint := terminal13Triangle0Vertices[1]!
  let c : QPoint := terminal13Triangle0Vertices[2]!
  have ha : a ∈ terminal13Triangle0Vertices := by simp [a, terminal13Triangle0Vertices]
  have hb : b ∈ terminal13Triangle0Vertices := by simp [b, terminal13Triangle0Vertices]
  have hc : c ∈ terminal13Triangle0Vertices := by simp [c, terminal13Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal13Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal13Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal13Triangle0])
  have hs1 : (terminal13Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal13Triangle0])
  have hs2 : (terminal13Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal13Triangle0])
  norm_num [terminal13Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal13Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal13Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal13Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal13_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal13Triangle1.carrier) : p ∈ rationalHull terminal13Triangle1Vertices := by
  let a : QPoint := terminal13Triangle1Vertices[0]!
  let b : QPoint := terminal13Triangle1Vertices[1]!
  let c : QPoint := terminal13Triangle1Vertices[2]!
  have ha : a ∈ terminal13Triangle1Vertices := by simp [a, terminal13Triangle1Vertices]
  have hb : b ∈ terminal13Triangle1Vertices := by simp [b, terminal13Triangle1Vertices]
  have hc : c ∈ terminal13Triangle1Vertices := by simp [c, terminal13Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal13Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal13Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal13Triangle1])
  have hs1 : (terminal13Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal13Triangle1])
  have hs2 : (terminal13Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal13Triangle1])
  norm_num [terminal13Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal13Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal13Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal13Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal14_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal14Triangle0.carrier) : p ∈ rationalHull terminal14Triangle0Vertices := by
  let a : QPoint := terminal14Triangle0Vertices[0]!
  let b : QPoint := terminal14Triangle0Vertices[1]!
  let c : QPoint := terminal14Triangle0Vertices[2]!
  have ha : a ∈ terminal14Triangle0Vertices := by simp [a, terminal14Triangle0Vertices]
  have hb : b ∈ terminal14Triangle0Vertices := by simp [b, terminal14Triangle0Vertices]
  have hc : c ∈ terminal14Triangle0Vertices := by simp [c, terminal14Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal14Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal14Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal14Triangle0])
  have hs1 : (terminal14Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal14Triangle0])
  have hs2 : (terminal14Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal14Triangle0])
  norm_num [terminal14Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal14Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal14Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal14Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal14_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal14Triangle1.carrier) : p ∈ rationalHull terminal14Triangle1Vertices := by
  let a : QPoint := terminal14Triangle1Vertices[0]!
  let b : QPoint := terminal14Triangle1Vertices[1]!
  let c : QPoint := terminal14Triangle1Vertices[2]!
  have ha : a ∈ terminal14Triangle1Vertices := by simp [a, terminal14Triangle1Vertices]
  have hb : b ∈ terminal14Triangle1Vertices := by simp [b, terminal14Triangle1Vertices]
  have hc : c ∈ terminal14Triangle1Vertices := by simp [c, terminal14Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal14Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal14Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal14Triangle1])
  have hs1 : (terminal14Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal14Triangle1])
  have hs2 : (terminal14Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal14Triangle1])
  norm_num [terminal14Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal14Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal14Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal14Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal15_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal15Triangle0.carrier) : p ∈ rationalHull terminal15Triangle0Vertices := by
  let a : QPoint := terminal15Triangle0Vertices[0]!
  let b : QPoint := terminal15Triangle0Vertices[1]!
  let c : QPoint := terminal15Triangle0Vertices[2]!
  have ha : a ∈ terminal15Triangle0Vertices := by simp [a, terminal15Triangle0Vertices]
  have hb : b ∈ terminal15Triangle0Vertices := by simp [b, terminal15Triangle0Vertices]
  have hc : c ∈ terminal15Triangle0Vertices := by simp [c, terminal15Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal15Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal15Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal15Triangle0])
  have hs1 : (terminal15Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal15Triangle0])
  have hs2 : (terminal15Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal15Triangle0])
  norm_num [terminal15Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal15Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal15Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal15Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal15_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal15Triangle1.carrier) : p ∈ rationalHull terminal15Triangle1Vertices := by
  let a : QPoint := terminal15Triangle1Vertices[0]!
  let b : QPoint := terminal15Triangle1Vertices[1]!
  let c : QPoint := terminal15Triangle1Vertices[2]!
  have ha : a ∈ terminal15Triangle1Vertices := by simp [a, terminal15Triangle1Vertices]
  have hb : b ∈ terminal15Triangle1Vertices := by simp [b, terminal15Triangle1Vertices]
  have hc : c ∈ terminal15Triangle1Vertices := by simp [c, terminal15Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal15Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal15Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal15Triangle1])
  have hs1 : (terminal15Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal15Triangle1])
  have hs2 : (terminal15Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal15Triangle1])
  norm_num [terminal15Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal15Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal15Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal15Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal16_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal16Triangle0.carrier) : p ∈ rationalHull terminal16Triangle0Vertices := by
  let a : QPoint := terminal16Triangle0Vertices[0]!
  let b : QPoint := terminal16Triangle0Vertices[1]!
  let c : QPoint := terminal16Triangle0Vertices[2]!
  have ha : a ∈ terminal16Triangle0Vertices := by simp [a, terminal16Triangle0Vertices]
  have hb : b ∈ terminal16Triangle0Vertices := by simp [b, terminal16Triangle0Vertices]
  have hc : c ∈ terminal16Triangle0Vertices := by simp [c, terminal16Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal16Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal16Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal16Triangle0])
  have hs1 : (terminal16Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal16Triangle0])
  have hs2 : (terminal16Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal16Triangle0])
  norm_num [terminal16Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal16Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal16Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal16Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal16_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal16Triangle1.carrier) : p ∈ rationalHull terminal16Triangle1Vertices := by
  let a : QPoint := terminal16Triangle1Vertices[0]!
  let b : QPoint := terminal16Triangle1Vertices[1]!
  let c : QPoint := terminal16Triangle1Vertices[2]!
  have ha : a ∈ terminal16Triangle1Vertices := by simp [a, terminal16Triangle1Vertices]
  have hb : b ∈ terminal16Triangle1Vertices := by simp [b, terminal16Triangle1Vertices]
  have hc : c ∈ terminal16Triangle1Vertices := by simp [c, terminal16Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal16Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal16Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal16Triangle1])
  have hs1 : (terminal16Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal16Triangle1])
  have hs2 : (terminal16Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal16Triangle1])
  norm_num [terminal16Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal16Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal16Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal16Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal17_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal17Triangle0.carrier) : p ∈ rationalHull terminal17Triangle0Vertices := by
  let a : QPoint := terminal17Triangle0Vertices[0]!
  let b : QPoint := terminal17Triangle0Vertices[1]!
  let c : QPoint := terminal17Triangle0Vertices[2]!
  have ha : a ∈ terminal17Triangle0Vertices := by simp [a, terminal17Triangle0Vertices]
  have hb : b ∈ terminal17Triangle0Vertices := by simp [b, terminal17Triangle0Vertices]
  have hc : c ∈ terminal17Triangle0Vertices := by simp [c, terminal17Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal17Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal17Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal17Triangle0])
  have hs1 : (terminal17Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal17Triangle0])
  have hs2 : (terminal17Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal17Triangle0])
  norm_num [terminal17Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal17Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal17Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal17Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal17_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal17Triangle1.carrier) : p ∈ rationalHull terminal17Triangle1Vertices := by
  let a : QPoint := terminal17Triangle1Vertices[0]!
  let b : QPoint := terminal17Triangle1Vertices[1]!
  let c : QPoint := terminal17Triangle1Vertices[2]!
  have ha : a ∈ terminal17Triangle1Vertices := by simp [a, terminal17Triangle1Vertices]
  have hb : b ∈ terminal17Triangle1Vertices := by simp [b, terminal17Triangle1Vertices]
  have hc : c ∈ terminal17Triangle1Vertices := by simp [c, terminal17Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal17Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal17Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal17Triangle1])
  have hs1 : (terminal17Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal17Triangle1])
  have hs2 : (terminal17Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal17Triangle1])
  norm_num [terminal17Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal17Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal17Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal17Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal18_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal18Triangle0.carrier) : p ∈ rationalHull terminal18Triangle0Vertices := by
  let a : QPoint := terminal18Triangle0Vertices[0]!
  let b : QPoint := terminal18Triangle0Vertices[1]!
  let c : QPoint := terminal18Triangle0Vertices[2]!
  have ha : a ∈ terminal18Triangle0Vertices := by simp [a, terminal18Triangle0Vertices]
  have hb : b ∈ terminal18Triangle0Vertices := by simp [b, terminal18Triangle0Vertices]
  have hc : c ∈ terminal18Triangle0Vertices := by simp [c, terminal18Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal18Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal18Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal18Triangle0])
  have hs1 : (terminal18Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal18Triangle0])
  have hs2 : (terminal18Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal18Triangle0])
  norm_num [terminal18Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal18Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal18Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal18Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal18_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal18Triangle1.carrier) : p ∈ rationalHull terminal18Triangle1Vertices := by
  let a : QPoint := terminal18Triangle1Vertices[0]!
  let b : QPoint := terminal18Triangle1Vertices[1]!
  let c : QPoint := terminal18Triangle1Vertices[2]!
  have ha : a ∈ terminal18Triangle1Vertices := by simp [a, terminal18Triangle1Vertices]
  have hb : b ∈ terminal18Triangle1Vertices := by simp [b, terminal18Triangle1Vertices]
  have hc : c ∈ terminal18Triangle1Vertices := by simp [c, terminal18Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal18Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal18Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal18Triangle1])
  have hs1 : (terminal18Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal18Triangle1])
  have hs2 : (terminal18Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal18Triangle1])
  norm_num [terminal18Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal18Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal18Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal18Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal19_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal19Triangle0.carrier) : p ∈ rationalHull terminal19Triangle0Vertices := by
  let a : QPoint := terminal19Triangle0Vertices[0]!
  let b : QPoint := terminal19Triangle0Vertices[1]!
  let c : QPoint := terminal19Triangle0Vertices[2]!
  have ha : a ∈ terminal19Triangle0Vertices := by simp [a, terminal19Triangle0Vertices]
  have hb : b ∈ terminal19Triangle0Vertices := by simp [b, terminal19Triangle0Vertices]
  have hc : c ∈ terminal19Triangle0Vertices := by simp [c, terminal19Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal19Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal19Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal19Triangle0])
  have hs1 : (terminal19Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal19Triangle0])
  have hs2 : (terminal19Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal19Triangle0])
  norm_num [terminal19Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal19Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal19Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal19Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal19_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal19Triangle1.carrier) : p ∈ rationalHull terminal19Triangle1Vertices := by
  let a : QPoint := terminal19Triangle1Vertices[0]!
  let b : QPoint := terminal19Triangle1Vertices[1]!
  let c : QPoint := terminal19Triangle1Vertices[2]!
  have ha : a ∈ terminal19Triangle1Vertices := by simp [a, terminal19Triangle1Vertices]
  have hb : b ∈ terminal19Triangle1Vertices := by simp [b, terminal19Triangle1Vertices]
  have hc : c ∈ terminal19Triangle1Vertices := by simp [c, terminal19Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal19Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal19Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal19Triangle1])
  have hs1 : (terminal19Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal19Triangle1])
  have hs2 : (terminal19Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal19Triangle1])
  norm_num [terminal19Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal19Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal19Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal19Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
