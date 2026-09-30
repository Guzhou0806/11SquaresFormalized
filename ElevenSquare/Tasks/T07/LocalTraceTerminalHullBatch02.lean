import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch02
import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Generated exact triangle-to-rational-hull certificates.  Each triangle's
three archived integer halfplanes imply its three oriented edge inequalities. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem terminal20_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal20Triangle0.carrier) : p ∈ rationalHull terminal20Triangle0Vertices := by
  let a : QPoint := terminal20Triangle0Vertices[0]!
  let b : QPoint := terminal20Triangle0Vertices[1]!
  let c : QPoint := terminal20Triangle0Vertices[2]!
  have ha : a ∈ terminal20Triangle0Vertices := by simp [a, terminal20Triangle0Vertices]
  have hb : b ∈ terminal20Triangle0Vertices := by simp [b, terminal20Triangle0Vertices]
  have hc : c ∈ terminal20Triangle0Vertices := by simp [c, terminal20Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal20Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal20Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal20Triangle0])
  have hs1 : (terminal20Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal20Triangle0])
  have hs2 : (terminal20Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal20Triangle0])
  norm_num [terminal20Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal20Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal20Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal20Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal20_triangle1_in_hull (p : Point)
    (hp : p ∈ terminal20Triangle1.carrier) : p ∈ rationalHull terminal20Triangle1Vertices := by
  let a : QPoint := terminal20Triangle1Vertices[0]!
  let b : QPoint := terminal20Triangle1Vertices[1]!
  let c : QPoint := terminal20Triangle1Vertices[2]!
  have ha : a ∈ terminal20Triangle1Vertices := by simp [a, terminal20Triangle1Vertices]
  have hb : b ∈ terminal20Triangle1Vertices := by simp [b, terminal20Triangle1Vertices]
  have hc : c ∈ terminal20Triangle1Vertices := by simp [c, terminal20Triangle1Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal20Triangle1Vertices, cross2, realPoint]
  have hs0 : (terminal20Triangle1[0]'(by decide)).contains p :=
    hp _ (by simp [terminal20Triangle1])
  have hs1 : (terminal20Triangle1[1]'(by decide)).contains p :=
    hp _ (by simp [terminal20Triangle1])
  have hs2 : (terminal20Triangle1[2]'(by decide)).contains p :=
    hp _ (by simp [terminal20Triangle1])
  norm_num [terminal20Triangle1, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal20Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal20Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal20Triangle1Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

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

theorem terminal22_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal22Triangle0.carrier) : p ∈ rationalHull terminal22Triangle0Vertices := by
  let a : QPoint := terminal22Triangle0Vertices[0]!
  let b : QPoint := terminal22Triangle0Vertices[1]!
  let c : QPoint := terminal22Triangle0Vertices[2]!
  have ha : a ∈ terminal22Triangle0Vertices := by simp [a, terminal22Triangle0Vertices]
  have hb : b ∈ terminal22Triangle0Vertices := by simp [b, terminal22Triangle0Vertices]
  have hc : c ∈ terminal22Triangle0Vertices := by simp [c, terminal22Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal22Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal22Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal22Triangle0])
  have hs1 : (terminal22Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal22Triangle0])
  have hs2 : (terminal22Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal22Triangle0])
  norm_num [terminal22Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal22Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal22Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal22Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal23_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal23Triangle0.carrier) : p ∈ rationalHull terminal23Triangle0Vertices := by
  let a : QPoint := terminal23Triangle0Vertices[0]!
  let b : QPoint := terminal23Triangle0Vertices[1]!
  let c : QPoint := terminal23Triangle0Vertices[2]!
  have ha : a ∈ terminal23Triangle0Vertices := by simp [a, terminal23Triangle0Vertices]
  have hb : b ∈ terminal23Triangle0Vertices := by simp [b, terminal23Triangle0Vertices]
  have hc : c ∈ terminal23Triangle0Vertices := by simp [c, terminal23Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal23Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal23Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal23Triangle0])
  have hs1 : (terminal23Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal23Triangle0])
  have hs2 : (terminal23Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal23Triangle0])
  norm_num [terminal23Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal23Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal23Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal23Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal24_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal24Triangle0.carrier) : p ∈ rationalHull terminal24Triangle0Vertices := by
  let a : QPoint := terminal24Triangle0Vertices[0]!
  let b : QPoint := terminal24Triangle0Vertices[1]!
  let c : QPoint := terminal24Triangle0Vertices[2]!
  have ha : a ∈ terminal24Triangle0Vertices := by simp [a, terminal24Triangle0Vertices]
  have hb : b ∈ terminal24Triangle0Vertices := by simp [b, terminal24Triangle0Vertices]
  have hc : c ∈ terminal24Triangle0Vertices := by simp [c, terminal24Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal24Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal24Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal24Triangle0])
  have hs1 : (terminal24Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal24Triangle0])
  have hs2 : (terminal24Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal24Triangle0])
  norm_num [terminal24Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal24Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal24Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal24Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal25_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal25Triangle0.carrier) : p ∈ rationalHull terminal25Triangle0Vertices := by
  let a : QPoint := terminal25Triangle0Vertices[0]!
  let b : QPoint := terminal25Triangle0Vertices[1]!
  let c : QPoint := terminal25Triangle0Vertices[2]!
  have ha : a ∈ terminal25Triangle0Vertices := by simp [a, terminal25Triangle0Vertices]
  have hb : b ∈ terminal25Triangle0Vertices := by simp [b, terminal25Triangle0Vertices]
  have hc : c ∈ terminal25Triangle0Vertices := by simp [c, terminal25Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal25Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal25Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal25Triangle0])
  have hs1 : (terminal25Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal25Triangle0])
  have hs2 : (terminal25Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal25Triangle0])
  norm_num [terminal25Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal25Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal25Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal25Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal26_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal26Triangle0.carrier) : p ∈ rationalHull terminal26Triangle0Vertices := by
  let a : QPoint := terminal26Triangle0Vertices[0]!
  let b : QPoint := terminal26Triangle0Vertices[1]!
  let c : QPoint := terminal26Triangle0Vertices[2]!
  have ha : a ∈ terminal26Triangle0Vertices := by simp [a, terminal26Triangle0Vertices]
  have hb : b ∈ terminal26Triangle0Vertices := by simp [b, terminal26Triangle0Vertices]
  have hc : c ∈ terminal26Triangle0Vertices := by simp [c, terminal26Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal26Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal26Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal26Triangle0])
  have hs1 : (terminal26Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal26Triangle0])
  have hs2 : (terminal26Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal26Triangle0])
  norm_num [terminal26Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal26Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal26Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal26Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal27_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal27Triangle0.carrier) : p ∈ rationalHull terminal27Triangle0Vertices := by
  let a : QPoint := terminal27Triangle0Vertices[0]!
  let b : QPoint := terminal27Triangle0Vertices[1]!
  let c : QPoint := terminal27Triangle0Vertices[2]!
  have ha : a ∈ terminal27Triangle0Vertices := by simp [a, terminal27Triangle0Vertices]
  have hb : b ∈ terminal27Triangle0Vertices := by simp [b, terminal27Triangle0Vertices]
  have hc : c ∈ terminal27Triangle0Vertices := by simp [c, terminal27Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal27Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal27Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal27Triangle0])
  have hs1 : (terminal27Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal27Triangle0])
  have hs2 : (terminal27Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal27Triangle0])
  norm_num [terminal27Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal27Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal27Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal27Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal28_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal28Triangle0.carrier) : p ∈ rationalHull terminal28Triangle0Vertices := by
  let a : QPoint := terminal28Triangle0Vertices[0]!
  let b : QPoint := terminal28Triangle0Vertices[1]!
  let c : QPoint := terminal28Triangle0Vertices[2]!
  have ha : a ∈ terminal28Triangle0Vertices := by simp [a, terminal28Triangle0Vertices]
  have hb : b ∈ terminal28Triangle0Vertices := by simp [b, terminal28Triangle0Vertices]
  have hc : c ∈ terminal28Triangle0Vertices := by simp [c, terminal28Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal28Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal28Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal28Triangle0])
  have hs1 : (terminal28Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal28Triangle0])
  have hs2 : (terminal28Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal28Triangle0])
  norm_num [terminal28Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal28Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal28Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal28Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

theorem terminal29_triangle0_in_hull (p : Point)
    (hp : p ∈ terminal29Triangle0.carrier) : p ∈ rationalHull terminal29Triangle0Vertices := by
  let a : QPoint := terminal29Triangle0Vertices[0]!
  let b : QPoint := terminal29Triangle0Vertices[1]!
  let c : QPoint := terminal29Triangle0Vertices[2]!
  have ha : a ∈ terminal29Triangle0Vertices := by simp [a, terminal29Triangle0Vertices]
  have hb : b ∈ terminal29Triangle0Vertices := by simp [b, terminal29Triangle0Vertices]
  have hc : c ∈ terminal29Triangle0Vertices := by simp [c, terminal29Triangle0Vertices]
  have hdet : 0 < cross2 (realPoint b-realPoint a) (realPoint c-realPoint a) := by
    norm_num [a, b, c, terminal29Triangle0Vertices, cross2, realPoint]
  have hs0 : (terminal29Triangle0[0]'(by decide)).contains p :=
    hp _ (by simp [terminal29Triangle0])
  have hs1 : (terminal29Triangle0[1]'(by decide)).contains p :=
    hp _ (by simp [terminal29Triangle0])
  have hs2 : (terminal29Triangle0[2]'(by decide)).contains p :=
    hp _ (by simp [terminal29Triangle0])
  norm_num [terminal29Triangle0, Halfplane.contains] at hs0 hs1 hs2
  apply rationalHull_triangle_of_edges a b c p ha hb hc hdet
  · norm_num [a, b, c, terminal29Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal29Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]
  · norm_num [a, b, c, terminal29Triangle0Vertices, cross2, realPoint]
    linarith only [hs0, hs1, hs2]

end
end ElevenSquare.Tasks.T07
