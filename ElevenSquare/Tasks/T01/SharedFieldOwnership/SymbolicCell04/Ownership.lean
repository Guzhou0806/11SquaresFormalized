import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime000
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime001
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime002
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime003
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime004
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime005
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime006
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime007
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime008
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime009
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime010
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime011
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime012
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime013
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Regime014

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def cert0 : AnchoredWallDirectionCertificate :=
  .split (3/8) (.split (5/32) (regime000) (regime001)) (.split (1/2) (regime002) (.split (5/8) (regime003) (regime004)))
theorem cert0_checked : cert0.Check 4 0 points 0 1 := by
  unfold cert0
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime000_checked
    · exact regime001_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime002_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact regime003_checked
      · exact regime004_checked

def cert1 : AnchoredWallDirectionCertificate :=
  .split (5/8) (.split (1/2) (regime005) (regime006)) (.split (3/4) (regime007) (regime008))
theorem cert1_checked : cert1.Check 4 1 points 0 1 := by
  unfold cert1
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime005_checked
    · exact regime006_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime007_checked
    · exact regime008_checked

def cert2 : AnchoredWallDirectionCertificate :=
  .split (1/8) (regime009) (.split (1/4) (regime010) (regime011))
theorem cert2_checked : cert2.Check 4 2 points 0 1 := by
  unfold cert2
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime009_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime010_checked
    · exact regime011_checked

def cert3 : AnchoredWallDirectionCertificate :=
  .split (1/8) (regime012) (.split (1/4) (regime013) (regime014))
theorem cert3_checked : cert3.Check 4 3 points 0 1 := by
  unfold cert3
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime012_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime013_checked
    · exact regime014_checked

def certs : Fin 4 → AnchoredWallDirectionCertificate := ![cert0, cert1, cert2, cert3]
theorem certs_checked : ∀ k, (certs k).Check 4 k points 0 1 := by
  intro k
  fin_cases k
  all_goals first | exact cert0_checked | exact cert1_checked | exact cert2_checked | exact cert3_checked

theorem initial_points_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ points, OpenSquare q (realPoint p) :=
  anchored_symbolic_wall_owned_points certs 4 points certs_checked q hcell hcont hchart

theorem gate_point005_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP005) := by
  exact initial_points_owned q hcell hcont hchart ownedP005 (by simp [points])

theorem gate_point006_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP006) := by
  exact initial_points_owned q hcell hcont hchart ownedP006 (by simp [points])

theorem gate_point007_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP007) := by
  exact initial_points_owned q hcell hcont hchart ownedP007 (by simp [points])

theorem gate_point008_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP008) := by
  exact initial_points_owned q hcell hcont hchart ownedP008 (by simp [points])

theorem gate_point010_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP010) := by
  exact initial_points_owned q hcell hcont hchart ownedP010 (by simp [points])

theorem gate_point011_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP011) := by
  exact initial_points_owned q hcell hcont hchart ownedP011 (by simp [points])

theorem gate_point012_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP012) := by
  exact initial_points_owned q hcell hcont hchart ownedP012 (by simp [points])

/-- Strict ownership of opposite cell 11 gate point 6, by half-turn. -/
theorem mirror_cell11_gate006_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_006) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_006)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_006 (by simp [points])
    simpa only [← mirrorP11_006_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_006 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 11 gate point 7, by half-turn. -/
theorem mirror_cell11_gate007_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_007) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_007)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_007 (by simp [points])
    simpa only [← mirrorP11_007_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_007 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 11 gate point 8, by half-turn. -/
theorem mirror_cell11_gate008_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_008) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_008)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_008 (by simp [points])
    simpa only [← mirrorP11_008_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_008 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 11 gate point 9, by half-turn. -/
theorem mirror_cell11_gate009_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_009) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_009)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_009 (by simp [points])
    simpa only [← mirrorP11_009_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_009 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 11 gate point 10, by half-turn. -/
theorem mirror_cell11_gate010_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_010) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_010)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_010 (by simp [points])
    simpa only [← mirrorP11_010_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_010 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 11 gate point 11, by half-turn. -/
theorem mirror_cell11_gate011_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_011) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_011)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_011 (by simp [points])
    simpa only [← mirrorP11_011_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_011 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 11 gate point 12, by half-turn. -/
theorem mirror_cell11_gate012_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_012) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_012)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_012 (by simp [points])
    simpa only [← mirrorP11_012_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_012 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 11 gate point 13, by half-turn. -/
theorem mirror_cell11_gate013_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP11_013) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 4 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP11_013)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP11_013 (by simp [points])
    simpa only [← mirrorP11_013_eq] using ho
  exact point_owned_of_halfTurn 4 originalP11_013 howned q
    (by simpa using hcell) hcont hchart

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
