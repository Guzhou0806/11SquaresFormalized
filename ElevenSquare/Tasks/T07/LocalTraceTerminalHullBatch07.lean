import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch07
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal250_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal250Triangle0.carrier) : p ∈ rationalHull terminal250Triangle0Vertices := by
  let a : QPoint := terminal250Triangle0Vertices[0]!
  let b : QPoint := terminal250Triangle0Vertices[1]!
  let c : QPoint := terminal250Triangle0Vertices[2]!
  have ha : a ∈ terminal250Triangle0Vertices := by simp [a, terminal250Triangle0Vertices]
  have hb : b ∈ terminal250Triangle0Vertices := by simp [b, terminal250Triangle0Vertices]
  have hc : c ∈ terminal250Triangle0Vertices := by simp [c, terminal250Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal250Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal250Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal250Triangle0])
  have hs1 : (terminal250Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal250Triangle0])
  have hs2 : (terminal250Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal250Triangle0])
  norm_num [terminal250Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal250Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal250Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal250Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal250_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal250Triangle1.carrier) : p ∈ rationalHull terminal250Triangle1Vertices := by
  let a : QPoint := terminal250Triangle1Vertices[0]!
  let b : QPoint := terminal250Triangle1Vertices[1]!
  let c : QPoint := terminal250Triangle1Vertices[2]!
  have ha : a ∈ terminal250Triangle1Vertices := by simp [a, terminal250Triangle1Vertices]
  have hb : b ∈ terminal250Triangle1Vertices := by simp [b, terminal250Triangle1Vertices]
  have hc : c ∈ terminal250Triangle1Vertices := by simp [c, terminal250Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal250Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal250Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal250Triangle1])
  have hs1 : (terminal250Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal250Triangle1])
  have hs2 : (terminal250Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal250Triangle1])
  norm_num [terminal250Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal250Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal250Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal250Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal251_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal251Triangle0.carrier) : p ∈ rationalHull terminal251Triangle0Vertices := by
  let a : QPoint := terminal251Triangle0Vertices[0]!
  let b : QPoint := terminal251Triangle0Vertices[1]!
  let c : QPoint := terminal251Triangle0Vertices[2]!
  have ha : a ∈ terminal251Triangle0Vertices := by simp [a, terminal251Triangle0Vertices]
  have hb : b ∈ terminal251Triangle0Vertices := by simp [b, terminal251Triangle0Vertices]
  have hc : c ∈ terminal251Triangle0Vertices := by simp [c, terminal251Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal251Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal251Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal251Triangle0])
  have hs1 : (terminal251Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal251Triangle0])
  have hs2 : (terminal251Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal251Triangle0])
  norm_num [terminal251Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal251Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal251Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal251Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal251_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal251Triangle1.carrier) : p ∈ rationalHull terminal251Triangle1Vertices := by
  let a : QPoint := terminal251Triangle1Vertices[0]!
  let b : QPoint := terminal251Triangle1Vertices[1]!
  let c : QPoint := terminal251Triangle1Vertices[2]!
  have ha : a ∈ terminal251Triangle1Vertices := by simp [a, terminal251Triangle1Vertices]
  have hb : b ∈ terminal251Triangle1Vertices := by simp [b, terminal251Triangle1Vertices]
  have hc : c ∈ terminal251Triangle1Vertices := by simp [c, terminal251Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal251Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal251Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal251Triangle1])
  have hs1 : (terminal251Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal251Triangle1])
  have hs2 : (terminal251Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal251Triangle1])
  norm_num [terminal251Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal251Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal251Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal251Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal252_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal252Triangle0.carrier) : p ∈ rationalHull terminal252Triangle0Vertices := by
  let a : QPoint := terminal252Triangle0Vertices[0]!
  let b : QPoint := terminal252Triangle0Vertices[1]!
  let c : QPoint := terminal252Triangle0Vertices[2]!
  have ha : a ∈ terminal252Triangle0Vertices := by simp [a, terminal252Triangle0Vertices]
  have hb : b ∈ terminal252Triangle0Vertices := by simp [b, terminal252Triangle0Vertices]
  have hc : c ∈ terminal252Triangle0Vertices := by simp [c, terminal252Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal252Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal252Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal252Triangle0])
  have hs1 : (terminal252Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal252Triangle0])
  have hs2 : (terminal252Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal252Triangle0])
  norm_num [terminal252Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal252Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal252Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal252Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal252_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal252Triangle1.carrier) : p ∈ rationalHull terminal252Triangle1Vertices := by
  let a : QPoint := terminal252Triangle1Vertices[0]!
  let b : QPoint := terminal252Triangle1Vertices[1]!
  let c : QPoint := terminal252Triangle1Vertices[2]!
  have ha : a ∈ terminal252Triangle1Vertices := by simp [a, terminal252Triangle1Vertices]
  have hb : b ∈ terminal252Triangle1Vertices := by simp [b, terminal252Triangle1Vertices]
  have hc : c ∈ terminal252Triangle1Vertices := by simp [c, terminal252Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal252Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal252Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal252Triangle1])
  have hs1 : (terminal252Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal252Triangle1])
  have hs2 : (terminal252Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal252Triangle1])
  norm_num [terminal252Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal252Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal252Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal252Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal253_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal253Triangle0.carrier) : p ∈ rationalHull terminal253Triangle0Vertices := by
  let a : QPoint := terminal253Triangle0Vertices[0]!
  let b : QPoint := terminal253Triangle0Vertices[1]!
  let c : QPoint := terminal253Triangle0Vertices[2]!
  have ha : a ∈ terminal253Triangle0Vertices := by simp [a, terminal253Triangle0Vertices]
  have hb : b ∈ terminal253Triangle0Vertices := by simp [b, terminal253Triangle0Vertices]
  have hc : c ∈ terminal253Triangle0Vertices := by simp [c, terminal253Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal253Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal253Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal253Triangle0])
  have hs1 : (terminal253Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal253Triangle0])
  have hs2 : (terminal253Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal253Triangle0])
  norm_num [terminal253Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal253Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal253Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal253Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal253_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal253Triangle1.carrier) : p ∈ rationalHull terminal253Triangle1Vertices := by
  let a : QPoint := terminal253Triangle1Vertices[0]!
  let b : QPoint := terminal253Triangle1Vertices[1]!
  let c : QPoint := terminal253Triangle1Vertices[2]!
  have ha : a ∈ terminal253Triangle1Vertices := by simp [a, terminal253Triangle1Vertices]
  have hb : b ∈ terminal253Triangle1Vertices := by simp [b, terminal253Triangle1Vertices]
  have hc : c ∈ terminal253Triangle1Vertices := by simp [c, terminal253Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal253Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal253Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal253Triangle1])
  have hs1 : (terminal253Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal253Triangle1])
  have hs2 : (terminal253Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal253Triangle1])
  norm_num [terminal253Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal253Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal253Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal253Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal254_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal254Triangle0.carrier) : p ∈ rationalHull terminal254Triangle0Vertices := by
  let a : QPoint := terminal254Triangle0Vertices[0]!
  let b : QPoint := terminal254Triangle0Vertices[1]!
  let c : QPoint := terminal254Triangle0Vertices[2]!
  have ha : a ∈ terminal254Triangle0Vertices := by simp [a, terminal254Triangle0Vertices]
  have hb : b ∈ terminal254Triangle0Vertices := by simp [b, terminal254Triangle0Vertices]
  have hc : c ∈ terminal254Triangle0Vertices := by simp [c, terminal254Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal254Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal254Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal254Triangle0])
  have hs1 : (terminal254Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal254Triangle0])
  have hs2 : (terminal254Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal254Triangle0])
  norm_num [terminal254Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal254Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal254Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal254Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal254_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal254Triangle1.carrier) : p ∈ rationalHull terminal254Triangle1Vertices := by
  let a : QPoint := terminal254Triangle1Vertices[0]!
  let b : QPoint := terminal254Triangle1Vertices[1]!
  let c : QPoint := terminal254Triangle1Vertices[2]!
  have ha : a ∈ terminal254Triangle1Vertices := by simp [a, terminal254Triangle1Vertices]
  have hb : b ∈ terminal254Triangle1Vertices := by simp [b, terminal254Triangle1Vertices]
  have hc : c ∈ terminal254Triangle1Vertices := by simp [c, terminal254Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal254Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal254Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal254Triangle1])
  have hs1 : (terminal254Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal254Triangle1])
  have hs2 : (terminal254Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal254Triangle1])
  norm_num [terminal254Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal254Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal254Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal254Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal255_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal255Triangle0.carrier) : p ∈ rationalHull terminal255Triangle0Vertices := by
  let a : QPoint := terminal255Triangle0Vertices[0]!
  let b : QPoint := terminal255Triangle0Vertices[1]!
  let c : QPoint := terminal255Triangle0Vertices[2]!
  have ha : a ∈ terminal255Triangle0Vertices := by simp [a, terminal255Triangle0Vertices]
  have hb : b ∈ terminal255Triangle0Vertices := by simp [b, terminal255Triangle0Vertices]
  have hc : c ∈ terminal255Triangle0Vertices := by simp [c, terminal255Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal255Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal255Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal255Triangle0])
  have hs1 : (terminal255Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal255Triangle0])
  have hs2 : (terminal255Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal255Triangle0])
  norm_num [terminal255Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal255Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal255Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal255Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal255_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal255Triangle1.carrier) : p ∈ rationalHull terminal255Triangle1Vertices := by
  let a : QPoint := terminal255Triangle1Vertices[0]!
  let b : QPoint := terminal255Triangle1Vertices[1]!
  let c : QPoint := terminal255Triangle1Vertices[2]!
  have ha : a ∈ terminal255Triangle1Vertices := by simp [a, terminal255Triangle1Vertices]
  have hb : b ∈ terminal255Triangle1Vertices := by simp [b, terminal255Triangle1Vertices]
  have hc : c ∈ terminal255Triangle1Vertices := by simp [c, terminal255Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal255Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal255Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal255Triangle1])
  have hs1 : (terminal255Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal255Triangle1])
  have hs2 : (terminal255Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal255Triangle1])
  norm_num [terminal255Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal255Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal255Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal255Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal256_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal256Triangle0.carrier) : p ∈ rationalHull terminal256Triangle0Vertices := by
  let a : QPoint := terminal256Triangle0Vertices[0]!
  let b : QPoint := terminal256Triangle0Vertices[1]!
  let c : QPoint := terminal256Triangle0Vertices[2]!
  have ha : a ∈ terminal256Triangle0Vertices := by simp [a, terminal256Triangle0Vertices]
  have hb : b ∈ terminal256Triangle0Vertices := by simp [b, terminal256Triangle0Vertices]
  have hc : c ∈ terminal256Triangle0Vertices := by simp [c, terminal256Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal256Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal256Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal256Triangle0])
  have hs1 : (terminal256Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal256Triangle0])
  have hs2 : (terminal256Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal256Triangle0])
  norm_num [terminal256Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal256Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal256Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal256Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal256_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal256Triangle1.carrier) : p ∈ rationalHull terminal256Triangle1Vertices := by
  let a : QPoint := terminal256Triangle1Vertices[0]!
  let b : QPoint := terminal256Triangle1Vertices[1]!
  let c : QPoint := terminal256Triangle1Vertices[2]!
  have ha : a ∈ terminal256Triangle1Vertices := by simp [a, terminal256Triangle1Vertices]
  have hb : b ∈ terminal256Triangle1Vertices := by simp [b, terminal256Triangle1Vertices]
  have hc : c ∈ terminal256Triangle1Vertices := by simp [c, terminal256Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal256Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal256Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal256Triangle1])
  have hs1 : (terminal256Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal256Triangle1])
  have hs2 : (terminal256Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal256Triangle1])
  norm_num [terminal256Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal256Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal256Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal256Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal257_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal257Triangle0.carrier) : p ∈ rationalHull terminal257Triangle0Vertices := by
  let a : QPoint := terminal257Triangle0Vertices[0]!
  let b : QPoint := terminal257Triangle0Vertices[1]!
  let c : QPoint := terminal257Triangle0Vertices[2]!
  have ha : a ∈ terminal257Triangle0Vertices := by simp [a, terminal257Triangle0Vertices]
  have hb : b ∈ terminal257Triangle0Vertices := by simp [b, terminal257Triangle0Vertices]
  have hc : c ∈ terminal257Triangle0Vertices := by simp [c, terminal257Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal257Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal257Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal257Triangle0])
  have hs1 : (terminal257Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal257Triangle0])
  have hs2 : (terminal257Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal257Triangle0])
  norm_num [terminal257Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal257Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal257Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal257Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal257_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal257Triangle1.carrier) : p ∈ rationalHull terminal257Triangle1Vertices := by
  let a : QPoint := terminal257Triangle1Vertices[0]!
  let b : QPoint := terminal257Triangle1Vertices[1]!
  let c : QPoint := terminal257Triangle1Vertices[2]!
  have ha : a ∈ terminal257Triangle1Vertices := by simp [a, terminal257Triangle1Vertices]
  have hb : b ∈ terminal257Triangle1Vertices := by simp [b, terminal257Triangle1Vertices]
  have hc : c ∈ terminal257Triangle1Vertices := by simp [c, terminal257Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal257Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal257Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal257Triangle1])
  have hs1 : (terminal257Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal257Triangle1])
  have hs2 : (terminal257Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal257Triangle1])
  norm_num [terminal257Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal257Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal257Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal257Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal258_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal258Triangle0.carrier) : p ∈ rationalHull terminal258Triangle0Vertices := by
  let a : QPoint := terminal258Triangle0Vertices[0]!
  let b : QPoint := terminal258Triangle0Vertices[1]!
  let c : QPoint := terminal258Triangle0Vertices[2]!
  have ha : a ∈ terminal258Triangle0Vertices := by simp [a, terminal258Triangle0Vertices]
  have hb : b ∈ terminal258Triangle0Vertices := by simp [b, terminal258Triangle0Vertices]
  have hc : c ∈ terminal258Triangle0Vertices := by simp [c, terminal258Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal258Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal258Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal258Triangle0])
  have hs1 : (terminal258Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal258Triangle0])
  have hs2 : (terminal258Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal258Triangle0])
  norm_num [terminal258Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal258Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal258Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal258Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal258_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal258Triangle1.carrier) : p ∈ rationalHull terminal258Triangle1Vertices := by
  let a : QPoint := terminal258Triangle1Vertices[0]!
  let b : QPoint := terminal258Triangle1Vertices[1]!
  let c : QPoint := terminal258Triangle1Vertices[2]!
  have ha : a ∈ terminal258Triangle1Vertices := by simp [a, terminal258Triangle1Vertices]
  have hb : b ∈ terminal258Triangle1Vertices := by simp [b, terminal258Triangle1Vertices]
  have hc : c ∈ terminal258Triangle1Vertices := by simp [c, terminal258Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal258Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal258Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal258Triangle1])
  have hs1 : (terminal258Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal258Triangle1])
  have hs2 : (terminal258Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal258Triangle1])
  norm_num [terminal258Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal258Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal258Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal258Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
