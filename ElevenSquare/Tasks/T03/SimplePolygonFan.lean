import ElevenSquare.Tasks.T03.TriangleCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def orientedChain (origin previous : QPoint) : List QPoint → Point → Prop
  | [], p => 0 ≤ orientedCross (realPoint previous) (realPoint origin) p
  | v::vs, p => 0 ≤ orientedCross (realPoint previous) (realPoint v) p ∧
      orientedChain origin v vs p

def edgeChainCheck (origin previous : QPoint) : List QPoint → List EdgePlane → Bool
  | [], [e] => e.check previous origin
  | v::vs, e::es => e.check previous v && edgeChainCheck origin v vs es
  | _, _ => false

theorem edgeChainCheck_sound (origin previous : QPoint) (vs : List QPoint)
    (es : List EdgePlane) (h : edgeChainCheck origin previous vs es = true)
    (p : Point) (hp : p ∈ IntegerCarrier (es.map EdgePlane.plane)) :
    orientedChain origin previous vs p := by
  induction vs generalizing previous es with
  | nil =>
    cases es with
    | nil => simp [edgeChainCheck] at h
    | cons e es =>
      cases es with
      | nil => exact e.sound previous origin h p (hp e.plane (by simp))
      | cons f rest => simp [edgeChainCheck] at h
  | cons v vs ih =>
    cases es with
    | nil => simp [edgeChainCheck] at h
    | cons e es =>
      simp only [edgeChainCheck,Bool.and_eq_true] at h
      exact ⟨e.sound previous v h.1 p (hp e.plane (by simp)),
        ih v es h.2 (fun l hl => hp l (List.mem_cons_of_mem _ hl))⟩

def fanOrientationCheck (a b : QPoint) : List QPoint → Bool
  | [] => false
  | [c] => decide (0 < rationalCross a b c)
  | c::d::vs => decide (0 < rationalCross a b c) && fanOrientationCheck a c (d::vs)

theorem orientedCross_reverse (a b p : Point) :
    orientedCross b a p = -orientedCross a b p := by
  dsimp [orientedCross]
  ring

theorem fanOrientationCheck_sound (a b : QPoint) (vs : List QPoint)
    (h : fanOrientationCheck a b vs = true) (F : Set Point) (hF : Convex ℝ F)
    (ha : realPoint a ∈ F) (hb : realPoint b ∈ F)
    (hv : ∀ v ∈ vs, realPoint v ∈ F) (p : Point)
    (hab : 0 ≤ orientedCross (realPoint a) (realPoint b) p)
    (hchain : orientedChain a b vs p) : p ∈ F := by
  induction vs generalizing b with
  | nil => simp [fanOrientationCheck] at h
  | cons c rest ih =>
    have hc : realPoint c ∈ F := hv c (by simp)
    have hbc : 0 ≤ orientedCross (realPoint b) (realPoint c) p := hchain.1
    cases rest with
    | nil =>
      have hor : 0 < rationalCross a b c := of_decide_eq_true h
      have hor' : (0:ℝ) < orientedCross (realPoint a) (realPoint b) (realPoint c) := by
        rw [← rationalCross_cast]
        exact_mod_cast hor
      exact triangle_mem_convex F hF _ _ _ p ha hb hc hor' hab hbc hchain.2
    | cons d rest =>
      simp only [fanOrientationCheck,Bool.and_eq_true] at h
      have hor : 0 < rationalCross a b c := of_decide_eq_true h.1
      have hor' : (0:ℝ) < orientedCross (realPoint a) (realPoint b) (realPoint c) := by
        rw [← rationalCross_cast]
        exact_mod_cast hor
      by_cases hca : 0 ≤ orientedCross (realPoint c) (realPoint a) p
      · exact triangle_mem_convex F hF _ _ _ p ha hb hc hor' hab hbc hca
      · have hac : 0 ≤ orientedCross (realPoint a) (realPoint c) p := by
          rw [orientedCross_reverse] at hca
          linarith
        exact ih c h.2 hc (fun v hv' => hv v (List.mem_cons_of_mem _ hv')) hac hchain.2

def polygonFanCheck : List QPoint → List EdgePlane → Bool
  | a::b::vs, es => fanOrientationCheck a b vs && edgeChainCheck a a (b::vs) es
  | _, _ => false

/-- The triangulation is proved once by induction. A concrete polygon supplies
only its original edge planes and positive fan orientations. No numerical
diagonal planes, split trees, or per-triangle Farkas witnesses are needed. -/
theorem polygonFanCheck_sound (vs : List QPoint) (es : List EdgePlane)
    (h : polygonFanCheck vs es = true) :
    IntegerCarrier (es.map EdgePlane.plane) ⊆ rationalHull vs := by
  cases vs with
  | nil => simp [polygonFanCheck] at h
  | cons a tail =>
    cases tail with
    | nil => simp [polygonFanCheck] at h
    | cons b vs =>
      simp only [polygonFanCheck,Bool.and_eq_true] at h
      intro p hp
      have hchain := edgeChainCheck_sound a a (b::vs) es h.2 p hp
      apply fanOrientationCheck_sound a b vs h.1 _ (convex_convexHull ℝ _) _ _ _ p hchain.1 hchain.2
      · exact subset_convexHull ℝ _ ⟨a,by simp,rfl⟩
      · exact subset_convexHull ℝ _ ⟨b,by simp,rfl⟩
      · intro v hv
        exact subset_convexHull ℝ _ ⟨v,by simp [hv],rfl⟩

end
end ElevenSquare.Pending.T03
