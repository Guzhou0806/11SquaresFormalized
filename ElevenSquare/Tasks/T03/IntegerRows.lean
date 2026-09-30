import ElevenSquare.Tasks.T03.PolygonCertificates
import ElevenSquare.Tasks.T03.SelfHullCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

structure IntegerRow where
  lo : ℚ
  hi : ℚ
  planes : List IntegerPlane

def IntegerRow.row (r : IntegerRow) : PoseRow :=
  ⟨r.lo,r.hi,r.planes.map IntegerPlane.rational⟩

theorem IntegerRow.center_mem (r : IntegerRow) (q : UnitSquare) (h : r.row.contains q) :
    q.center ∈ IntegerCarrier r.planes := by
  rw [integerCarrier_as_polygon]
  exact h.1

def IntegerRow.intervalCheck (r : IntegerRow) (lo hi : ℚ) : Bool :=
  decide (lo ≤ r.lo ∧ r.hi ≤ hi)

theorem IntegerRow.interval_sound (r : IntegerRow) (lo hi : ℚ)
    (h : r.intervalCheck lo hi = true) (q : UnitSquare) (hq : r.row.contains q) :
    ∃ t : ℝ, (lo:ℝ) ≤ t ∧ t ≤ (hi:ℝ) ∧ q.axis=chartAxis t := by
  obtain ⟨hlo,hhi⟩ := of_decide_eq_true h
  obtain ⟨t,ht0,ht1,hta,htb,htq⟩ := hq.2
  have hlo' : (lo:ℝ) ≤ (r.lo:ℝ) := by exact_mod_cast hlo
  have hhi' : (r.hi:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hhi
  exact ⟨t,le_trans hlo' hta,le_trans htb hhi',htq⟩

def selfHullCutsCheck (vs : List QPoint) (lo hi : ℚ) (cuts : List SelfHullCutCertificate) : Bool :=
  decide (∀ w ∈ cuts, w.check vs = true ∧ w.radius.lo=lo ∧ w.radius.hi=hi)

theorem selfHullCutsCheck_sound (vs : List QPoint) (lo hi : ℚ)
    (cuts : List SelfHullCutCertificate) (h : selfHullCutsCheck vs lo hi cuts = true)
    (q : UnitSquare) (t : ℝ) (hq : q.axis=chartAxis t)
    (ht0 : (lo:ℝ) ≤ t) (ht1 : t ≤ (hi:ℝ))
    (hold : rationalHull vs ⊆ {p | OpenSquare q p}) :
    q.center ∈ IntegerCarrier (cuts.map SelfHullCutCertificate.plane) := by
  intro l hl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hl
  obtain ⟨hcheck,hlo,hhi⟩ := (of_decide_eq_true h) w hw
  exact w.sound vs hcheck q t hold hq (by rwa [hlo]) (by rwa [hhi])

structure RowInputCertificate where
  lo : ℚ
  hi : ℚ
  cuts : List SelfHullCutCertificate
  domain : List IntegerPlane
  implications : List LinearCertificate

def RowInputCertificate.check (w : RowInputCertificate) (r : IntegerRow) (vs : List QPoint) : Bool :=
  r.intervalCheck w.lo w.hi && selfHullCutsCheck vs w.lo w.hi w.cuts &&
    planeImplicationsCheck (r.planes++w.cuts.map SelfHullCutCertificate.plane) w.domain w.implications

theorem RowInputCertificate.sound (w : RowInputCertificate) (r : IntegerRow) (vs : List QPoint)
    (h : w.check r vs = true) (q : UnitSquare) (hq : r.row.contains q)
    (hold : rationalHull vs ⊆ {p | OpenSquare q p}) :
    q.center ∈ IntegerCarrier w.domain ∧
      ∃ t : ℝ, (w.lo:ℝ) ≤ t ∧ t ≤ (w.hi:ℝ) ∧ q.axis=chartAxis t := by
  simp only [RowInputCertificate.check,Bool.and_eq_true] at h
  obtain ⟨t,ht0,ht1,htq⟩ := r.interval_sound w.lo w.hi h.1.1 q hq
  have hcuts := selfHullCutsCheck_sound vs w.lo w.hi w.cuts h.1.2 q t htq ht0 ht1 hold
  have hp : q.center ∈ IntegerCarrier (r.planes++w.cuts.map SelfHullCutCertificate.plane) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact r.center_mem q hq l hl
    · exact hcuts l hl
  exact ⟨planeImplicationsCheck_sound _ _ w.implications h.2 hp,t,ht0,ht1,htq⟩

end
end ElevenSquare.Pending.T03
