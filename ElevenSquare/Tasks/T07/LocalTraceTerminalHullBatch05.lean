import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch05
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal230_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal230Triangle0.carrier) : p ∈ rationalHull terminal230Triangle0Vertices := by
  let a : QPoint := terminal230Triangle0Vertices[0]!
  let b : QPoint := terminal230Triangle0Vertices[1]!
  let c : QPoint := terminal230Triangle0Vertices[2]!
  have ha : a ∈ terminal230Triangle0Vertices := by simp [a, terminal230Triangle0Vertices]
  have hb : b ∈ terminal230Triangle0Vertices := by simp [b, terminal230Triangle0Vertices]
  have hc : c ∈ terminal230Triangle0Vertices := by simp [c, terminal230Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal230Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal230Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal230Triangle0])
  have hs1 : (terminal230Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal230Triangle0])
  have hs2 : (terminal230Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal230Triangle0])
  norm_num [terminal230Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal230Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal230Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal230Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal231_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal231Triangle0.carrier) : p ∈ rationalHull terminal231Triangle0Vertices := by
  let a : QPoint := terminal231Triangle0Vertices[0]!
  let b : QPoint := terminal231Triangle0Vertices[1]!
  let c : QPoint := terminal231Triangle0Vertices[2]!
  have ha : a ∈ terminal231Triangle0Vertices := by simp [a, terminal231Triangle0Vertices]
  have hb : b ∈ terminal231Triangle0Vertices := by simp [b, terminal231Triangle0Vertices]
  have hc : c ∈ terminal231Triangle0Vertices := by simp [c, terminal231Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal231Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal231Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal231Triangle0])
  have hs1 : (terminal231Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal231Triangle0])
  have hs2 : (terminal231Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal231Triangle0])
  norm_num [terminal231Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal231Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal231Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal231Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal232_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal232Triangle0.carrier) : p ∈ rationalHull terminal232Triangle0Vertices := by
  let a : QPoint := terminal232Triangle0Vertices[0]!
  let b : QPoint := terminal232Triangle0Vertices[1]!
  let c : QPoint := terminal232Triangle0Vertices[2]!
  have ha : a ∈ terminal232Triangle0Vertices := by simp [a, terminal232Triangle0Vertices]
  have hb : b ∈ terminal232Triangle0Vertices := by simp [b, terminal232Triangle0Vertices]
  have hc : c ∈ terminal232Triangle0Vertices := by simp [c, terminal232Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal232Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal232Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal232Triangle0])
  have hs1 : (terminal232Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal232Triangle0])
  have hs2 : (terminal232Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal232Triangle0])
  norm_num [terminal232Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal232Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal232Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal232Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal233_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal233Triangle0.carrier) : p ∈ rationalHull terminal233Triangle0Vertices := by
  let a : QPoint := terminal233Triangle0Vertices[0]!
  let b : QPoint := terminal233Triangle0Vertices[1]!
  let c : QPoint := terminal233Triangle0Vertices[2]!
  have ha : a ∈ terminal233Triangle0Vertices := by simp [a, terminal233Triangle0Vertices]
  have hb : b ∈ terminal233Triangle0Vertices := by simp [b, terminal233Triangle0Vertices]
  have hc : c ∈ terminal233Triangle0Vertices := by simp [c, terminal233Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal233Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal233Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal233Triangle0])
  have hs1 : (terminal233Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal233Triangle0])
  have hs2 : (terminal233Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal233Triangle0])
  norm_num [terminal233Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal233Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal233Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal233Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal234_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal234Triangle0.carrier) : p ∈ rationalHull terminal234Triangle0Vertices := by
  let a : QPoint := terminal234Triangle0Vertices[0]!
  let b : QPoint := terminal234Triangle0Vertices[1]!
  let c : QPoint := terminal234Triangle0Vertices[2]!
  have ha : a ∈ terminal234Triangle0Vertices := by simp [a, terminal234Triangle0Vertices]
  have hb : b ∈ terminal234Triangle0Vertices := by simp [b, terminal234Triangle0Vertices]
  have hc : c ∈ terminal234Triangle0Vertices := by simp [c, terminal234Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal234Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal234Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal234Triangle0])
  have hs1 : (terminal234Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal234Triangle0])
  have hs2 : (terminal234Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal234Triangle0])
  norm_num [terminal234Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal234Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal234Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal234Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal235_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal235Triangle0.carrier) : p ∈ rationalHull terminal235Triangle0Vertices := by
  let a : QPoint := terminal235Triangle0Vertices[0]!
  let b : QPoint := terminal235Triangle0Vertices[1]!
  let c : QPoint := terminal235Triangle0Vertices[2]!
  have ha : a ∈ terminal235Triangle0Vertices := by simp [a, terminal235Triangle0Vertices]
  have hb : b ∈ terminal235Triangle0Vertices := by simp [b, terminal235Triangle0Vertices]
  have hc : c ∈ terminal235Triangle0Vertices := by simp [c, terminal235Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal235Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal235Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal235Triangle0])
  have hs1 : (terminal235Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal235Triangle0])
  have hs2 : (terminal235Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal235Triangle0])
  norm_num [terminal235Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal235Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal235Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal235Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal236_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal236Triangle0.carrier) : p ∈ rationalHull terminal236Triangle0Vertices := by
  let a : QPoint := terminal236Triangle0Vertices[0]!
  let b : QPoint := terminal236Triangle0Vertices[1]!
  let c : QPoint := terminal236Triangle0Vertices[2]!
  have ha : a ∈ terminal236Triangle0Vertices := by simp [a, terminal236Triangle0Vertices]
  have hb : b ∈ terminal236Triangle0Vertices := by simp [b, terminal236Triangle0Vertices]
  have hc : c ∈ terminal236Triangle0Vertices := by simp [c, terminal236Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal236Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal236Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal236Triangle0])
  have hs1 : (terminal236Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal236Triangle0])
  have hs2 : (terminal236Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal236Triangle0])
  norm_num [terminal236Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal236Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal236Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal236Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal237_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal237Triangle0.carrier) : p ∈ rationalHull terminal237Triangle0Vertices := by
  let a : QPoint := terminal237Triangle0Vertices[0]!
  let b : QPoint := terminal237Triangle0Vertices[1]!
  let c : QPoint := terminal237Triangle0Vertices[2]!
  have ha : a ∈ terminal237Triangle0Vertices := by simp [a, terminal237Triangle0Vertices]
  have hb : b ∈ terminal237Triangle0Vertices := by simp [b, terminal237Triangle0Vertices]
  have hc : c ∈ terminal237Triangle0Vertices := by simp [c, terminal237Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal237Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal237Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal237Triangle0])
  have hs1 : (terminal237Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal237Triangle0])
  have hs2 : (terminal237Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal237Triangle0])
  norm_num [terminal237Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal237Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal237Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal237Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal238_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal238Triangle0.carrier) : p ∈ rationalHull terminal238Triangle0Vertices := by
  let a : QPoint := terminal238Triangle0Vertices[0]!
  let b : QPoint := terminal238Triangle0Vertices[1]!
  let c : QPoint := terminal238Triangle0Vertices[2]!
  have ha : a ∈ terminal238Triangle0Vertices := by simp [a, terminal238Triangle0Vertices]
  have hb : b ∈ terminal238Triangle0Vertices := by simp [b, terminal238Triangle0Vertices]
  have hc : c ∈ terminal238Triangle0Vertices := by simp [c, terminal238Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal238Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal238Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal238Triangle0])
  have hs1 : (terminal238Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal238Triangle0])
  have hs2 : (terminal238Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal238Triangle0])
  norm_num [terminal238Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal238Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal238Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal238Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal239_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal239Triangle0.carrier) : p ∈ rationalHull terminal239Triangle0Vertices := by
  let a : QPoint := terminal239Triangle0Vertices[0]!
  let b : QPoint := terminal239Triangle0Vertices[1]!
  let c : QPoint := terminal239Triangle0Vertices[2]!
  have ha : a ∈ terminal239Triangle0Vertices := by simp [a, terminal239Triangle0Vertices]
  have hb : b ∈ terminal239Triangle0Vertices := by simp [b, terminal239Triangle0Vertices]
  have hc : c ∈ terminal239Triangle0Vertices := by simp [c, terminal239Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal239Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal239Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal239Triangle0])
  have hs1 : (terminal239Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal239Triangle0])
  have hs2 : (terminal239Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal239Triangle0])
  norm_num [terminal239Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal239Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal239Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal239Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
