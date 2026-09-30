import ElevenSquare.Pending.S07_EdgeCertificate
namespace ElevenSquare.Pending

def slabCheck (lower upper : IntegerPlane) (ll lr ul ur : FractionPoint) : Bool :=
  decide (lower.b<0 ∧ 0<upper.b ∧ fractionLT ll.nx ll.dx lr.nx lr.dx=true ∧
    fractionEQ ll.nx ll.dx ul.nx ul.dx=true ∧ fractionEQ lr.nx lr.dx ur.nx ur.dx=true ∧
    ll.onPlaneCheck lower=true ∧ lr.onPlaneCheck lower=true ∧
    ul.onPlaneCheck upper=true ∧ ur.onPlaneCheck upper=true)

theorem slabCheck_sound {C : Set Point} (hc : Convex ℝ C)
    (lower upper : IntegerPlane) (ll lr ul ur : FractionPoint)
    (h : slabCheck lower upper ll lr ul ur = true)
    (hll : ll.real∈C) (hlr : lr.real∈C) (hul : ul.real∈C) (hur : ur.real∈C)
    (p : Point) (hl : lower.rational.contains p) (hu : upper.rational.contains p)
    (hx0 : ll.real.1≤p.1) (hx1 : p.1≤lr.real.1) : p∈C := by
  obtain ⟨hlb,hub,hw,heL,heR,hllLine,hlrLine,hulLine,hurLine⟩ := of_decide_eq_true h
  have hlb' : (lower.b:ℝ)<0 := by exact_mod_cast hlb
  have hub' : (0:ℝ)<(upper.b:ℝ) := by exact_mod_cast hub
  have hwidth := ll.xLT lr hw
  have hleft := ll.xEQ ul heL
  have hright := lr.xEQ ur heR
  have hll' := ll.onPlaneCheck_sound lower hllLine
  have hlr' := lr.onPlaneCheck_sound lower hlrLine
  have hul' := ul.onPlaneCheck_sound upper hulLine
  have hur' := ur.onPlaneCheck_sound upper hurLine
  rw [← ll.real_correct] at hll'
  rw [← lr.real_correct] at hlr'
  rw [← ul.real_correct, ← hleft] at hul'
  rw [← ur.real_correct, ← hright] at hur'
  have hulMem : (ll.real.1,ul.real.2)∈C := by rw [hleft]; exact hul
  have hurMem : (lr.real.1,ur.real.2)∈C := by rw [hright]; exact hur
  apply convex_trapezoid hc ll.real.1 lr.real.1 ll.real.2 lr.real.2 ul.real.2 ur.real.2
    p.1 p.2 hwidth hll hlr hulMem hurMem hx0 hx1
  · exact lower_edge_bound lower.a lower.b lower.c _ _ _ _ _ _ hwidth.le hlb' hll' hlr' hl
  · exact upper_edge_bound upper.a upper.b upper.c _ _ _ _ _ _ hwidth.le hub' hul' hur' hu

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.slabCheck_sound
