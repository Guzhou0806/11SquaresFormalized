import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch03
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal30_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal30Triangle0.carrier) : p ∈ rationalHull terminal30Triangle0Vertices := by
  let a : QPoint := terminal30Triangle0Vertices[0]!
  let b : QPoint := terminal30Triangle0Vertices[1]!
  let c : QPoint := terminal30Triangle0Vertices[2]!
  have ha : a ∈ terminal30Triangle0Vertices := by simp [a, terminal30Triangle0Vertices]
  have hb : b ∈ terminal30Triangle0Vertices := by simp [b, terminal30Triangle0Vertices]
  have hc : c ∈ terminal30Triangle0Vertices := by simp [c, terminal30Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal30Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal30Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal30Triangle0])
  have hs1 : (terminal30Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal30Triangle0])
  have hs2 : (terminal30Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal30Triangle0])
  norm_num [terminal30Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal30Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal30Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal30Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal31_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal31Triangle0.carrier) : p ∈ rationalHull terminal31Triangle0Vertices := by
  let a : QPoint := terminal31Triangle0Vertices[0]!
  let b : QPoint := terminal31Triangle0Vertices[1]!
  let c : QPoint := terminal31Triangle0Vertices[2]!
  have ha : a ∈ terminal31Triangle0Vertices := by simp [a, terminal31Triangle0Vertices]
  have hb : b ∈ terminal31Triangle0Vertices := by simp [b, terminal31Triangle0Vertices]
  have hc : c ∈ terminal31Triangle0Vertices := by simp [c, terminal31Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal31Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal31Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal31Triangle0])
  have hs1 : (terminal31Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal31Triangle0])
  have hs2 : (terminal31Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal31Triangle0])
  norm_num [terminal31Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal31Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal31Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal31Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal32_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal32Triangle0.carrier) : p ∈ rationalHull terminal32Triangle0Vertices := by
  let a : QPoint := terminal32Triangle0Vertices[0]!
  let b : QPoint := terminal32Triangle0Vertices[1]!
  let c : QPoint := terminal32Triangle0Vertices[2]!
  have ha : a ∈ terminal32Triangle0Vertices := by simp [a, terminal32Triangle0Vertices]
  have hb : b ∈ terminal32Triangle0Vertices := by simp [b, terminal32Triangle0Vertices]
  have hc : c ∈ terminal32Triangle0Vertices := by simp [c, terminal32Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal32Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal32Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal32Triangle0])
  have hs1 : (terminal32Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal32Triangle0])
  have hs2 : (terminal32Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal32Triangle0])
  norm_num [terminal32Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal32Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal32Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal32Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal33_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal33Triangle0.carrier) : p ∈ rationalHull terminal33Triangle0Vertices := by
  let a : QPoint := terminal33Triangle0Vertices[0]!
  let b : QPoint := terminal33Triangle0Vertices[1]!
  let c : QPoint := terminal33Triangle0Vertices[2]!
  have ha : a ∈ terminal33Triangle0Vertices := by simp [a, terminal33Triangle0Vertices]
  have hb : b ∈ terminal33Triangle0Vertices := by simp [b, terminal33Triangle0Vertices]
  have hc : c ∈ terminal33Triangle0Vertices := by simp [c, terminal33Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal33Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal33Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal33Triangle0])
  have hs1 : (terminal33Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal33Triangle0])
  have hs2 : (terminal33Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal33Triangle0])
  norm_num [terminal33Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal33Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal33Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal33Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal34_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal34Triangle0.carrier) : p ∈ rationalHull terminal34Triangle0Vertices := by
  let a : QPoint := terminal34Triangle0Vertices[0]!
  let b : QPoint := terminal34Triangle0Vertices[1]!
  let c : QPoint := terminal34Triangle0Vertices[2]!
  have ha : a ∈ terminal34Triangle0Vertices := by simp [a, terminal34Triangle0Vertices]
  have hb : b ∈ terminal34Triangle0Vertices := by simp [b, terminal34Triangle0Vertices]
  have hc : c ∈ terminal34Triangle0Vertices := by simp [c, terminal34Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal34Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal34Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal34Triangle0])
  have hs1 : (terminal34Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal34Triangle0])
  have hs2 : (terminal34Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal34Triangle0])
  norm_num [terminal34Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal34Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal34Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal34Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal35_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal35Triangle0.carrier) : p ∈ rationalHull terminal35Triangle0Vertices := by
  let a : QPoint := terminal35Triangle0Vertices[0]!
  let b : QPoint := terminal35Triangle0Vertices[1]!
  let c : QPoint := terminal35Triangle0Vertices[2]!
  have ha : a ∈ terminal35Triangle0Vertices := by simp [a, terminal35Triangle0Vertices]
  have hb : b ∈ terminal35Triangle0Vertices := by simp [b, terminal35Triangle0Vertices]
  have hc : c ∈ terminal35Triangle0Vertices := by simp [c, terminal35Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal35Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal35Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal35Triangle0])
  have hs1 : (terminal35Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal35Triangle0])
  have hs2 : (terminal35Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal35Triangle0])
  norm_num [terminal35Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal35Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal35Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal35Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal36_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal36Triangle0.carrier) : p ∈ rationalHull terminal36Triangle0Vertices := by
  let a : QPoint := terminal36Triangle0Vertices[0]!
  let b : QPoint := terminal36Triangle0Vertices[1]!
  let c : QPoint := terminal36Triangle0Vertices[2]!
  have ha : a ∈ terminal36Triangle0Vertices := by simp [a, terminal36Triangle0Vertices]
  have hb : b ∈ terminal36Triangle0Vertices := by simp [b, terminal36Triangle0Vertices]
  have hc : c ∈ terminal36Triangle0Vertices := by simp [c, terminal36Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal36Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal36Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal36Triangle0])
  have hs1 : (terminal36Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal36Triangle0])
  have hs2 : (terminal36Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal36Triangle0])
  norm_num [terminal36Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal36Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal36Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal36Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal37_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal37Triangle0.carrier) : p ∈ rationalHull terminal37Triangle0Vertices := by
  let a : QPoint := terminal37Triangle0Vertices[0]!
  let b : QPoint := terminal37Triangle0Vertices[1]!
  let c : QPoint := terminal37Triangle0Vertices[2]!
  have ha : a ∈ terminal37Triangle0Vertices := by simp [a, terminal37Triangle0Vertices]
  have hb : b ∈ terminal37Triangle0Vertices := by simp [b, terminal37Triangle0Vertices]
  have hc : c ∈ terminal37Triangle0Vertices := by simp [c, terminal37Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal37Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal37Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal37Triangle0])
  have hs1 : (terminal37Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal37Triangle0])
  have hs2 : (terminal37Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal37Triangle0])
  norm_num [terminal37Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal37Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal37Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal37Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal38_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal38Triangle0.carrier) : p ∈ rationalHull terminal38Triangle0Vertices := by
  let a : QPoint := terminal38Triangle0Vertices[0]!
  let b : QPoint := terminal38Triangle0Vertices[1]!
  let c : QPoint := terminal38Triangle0Vertices[2]!
  have ha : a ∈ terminal38Triangle0Vertices := by simp [a, terminal38Triangle0Vertices]
  have hb : b ∈ terminal38Triangle0Vertices := by simp [b, terminal38Triangle0Vertices]
  have hc : c ∈ terminal38Triangle0Vertices := by simp [c, terminal38Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal38Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal38Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal38Triangle0])
  have hs1 : (terminal38Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal38Triangle0])
  have hs2 : (terminal38Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal38Triangle0])
  norm_num [terminal38Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal38Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal38Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal38Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal39_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal39Triangle0.carrier) : p ∈ rationalHull terminal39Triangle0Vertices := by
  let a : QPoint := terminal39Triangle0Vertices[0]!
  let b : QPoint := terminal39Triangle0Vertices[1]!
  let c : QPoint := terminal39Triangle0Vertices[2]!
  have ha : a ∈ terminal39Triangle0Vertices := by simp [a, terminal39Triangle0Vertices]
  have hb : b ∈ terminal39Triangle0Vertices := by simp [b, terminal39Triangle0Vertices]
  have hc : c ∈ terminal39Triangle0Vertices := by simp [c, terminal39Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal39Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal39Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal39Triangle0])
  have hs1 : (terminal39Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal39Triangle0])
  have hs2 : (terminal39Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal39Triangle0])
  norm_num [terminal39Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal39Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal39Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal39Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
