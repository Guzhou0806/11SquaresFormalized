import ElevenSquare.Tasks.T01.SymbolicWallCertificate

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

deriving instance DecidableEq for SymbolicWallFacet

/-- An angle cover records actual supporting-pair regimes, with closed splits.
An irrational change of active pair is handled inside a crossing leaf. -/
inductive WallDirectionCertificate where
  | ordinary (f g : SymbolicWallFacet)
  | crossing (f g h : SymbolicWallFacet) (ratio : ℚ)
  | split (mid : ℚ) (left right : WallDirectionCertificate)

def WallDirectionCertificate.Check (cert : WallDirectionCertificate)
    (cell : Fin 16) (k : Fin 4) (points : List QPoint) (l u : ℚ) : Prop :=
  match cert with
  | .ordinary f g =>
      f ∈ symbolicWallSlab cell ∧ g ∈ symbolicWallSlab cell ∧
        ∀ p ∈ points, WallDualCheck f g k p l u
  | .crossing f g h r =>
      f ∈ symbolicWallSlab cell ∧ g ∈ symbolicWallSlab cell ∧
        h ∈ symbolicWallSlab cell ∧ ∀ p ∈ points, WallDualCrossingCheck f g h k p l u r
  | .split mid left right =>
      l ≤ mid ∧ mid ≤ u ∧ left.Check cell k points l mid ∧ right.Check cell k points mid u

instance wallDirectionCertificateCheckDecidable
    (cert : WallDirectionCertificate) (cell : Fin 16) (k : Fin 4)
    (points : List QPoint) (l u : ℚ) : Decidable (cert.Check cell k points l u) := by
  induction cert generalizing l u with
  | ordinary f g => unfold WallDirectionCertificate.Check; infer_instance
  | crossing f g h r => unfold WallDirectionCertificate.Check; infer_instance
  | split mid left right ihl ihr =>
    unfold WallDirectionCertificate.Check
    exact @instDecidableAnd _ _ (inferInstance) (@instDecidableAnd _ _ (inferInstance)
      (@instDecidableAnd _ _ (ihl l mid) (ihr mid u)))

def WallDirectionCertificate.regimeCount : WallDirectionCertificate → ℕ
  | .ordinary _ _ => 1
  | .crossing _ _ _ _ => 1
  | .split _ left right => left.regimeCount + right.regimeCount

theorem wall_direction_certificate_sound (cert : WallDirectionCertificate)
    (cell : Fin 16) (k : Fin 4) (points : List QPoint) (l u : ℚ)
    (hc : cert.Check cell k points l u) (p : QPoint) (hp : p ∈ points)
    (t : ℝ) (hl : (l:ℝ) ≤ t) (hu : t ≤ (u:ℝ)) :
    ∃ f ∈ symbolicWallSlab cell, ∃ g ∈ symbolicWallSlab cell, WallDualSupports f g k p t := by
  induction cert generalizing l u with
  | ordinary f g =>
    exact ⟨f, hc.1, g, hc.2.1, wall_dual_check_sound f g k p l u (hc.2.2 p hp) t hl hu⟩
  | crossing f g h r =>
    rcases wall_dual_crossing_check_sound f g h k p l u r (hc.2.2.2 p hp) t hl hu with hh | hh
    · exact ⟨f, hc.1, g, hc.2.1, hh⟩
    · exact ⟨g, hc.2.1, h, hc.2.2.1, hh⟩
  | split mid left right ihl ihr =>
    by_cases hm : t ≤ (mid:ℝ)
    · exact ihl l mid hc.2.2.1 hl hm
    · exact ihr mid u hc.2.2.2 (le_of_not_ge hm) hu

/-- Four complete angle covers prove all listed points owned throughout a cell. -/
theorem symbolic_wall_owned_points (certs : Fin 4 → WallDirectionCertificate)
    (cell : Fin 16) (points : List QPoint)
    (hc : ∀ k, (certs k).Check cell k points 0 1)
    (q : UnitSquare) (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ points, OpenSquare q (realPoint p) := by
  obtain ⟨t, ht0, ht1, ha⟩ := hchart
  intro p hp
  apply symbolic_wall_point_owned q cell (realPoint p) t ha hcont hcell
  intro k
  obtain ⟨f, hf, g, hg, hw⟩ :=
    wall_direction_certificate_sound (certs k) cell k points 0 1 (hc k) p hp t
      (by simpa using ht0) (by simpa using ht1)
  exact ⟨f, hf, g, hg, hw⟩

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.wall_direction_certificate_sound
#print axioms ElevenSquare.Tasks.T01.symbolic_wall_owned_points
