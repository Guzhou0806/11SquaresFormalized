import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime000
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime001
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime002
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime003
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime004
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime005
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime006
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime007
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime008
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime009
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime010
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime011
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Regime012

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def cert0 : AnchoredWallDirectionCertificate :=
  .split (1/2) (regime000) (.split (5/8) (regime001) (regime002))
theorem cert0_checked : cert0.Check 3 0 points 0 1 := by
  unfold cert0
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime000_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime001_checked
    · exact regime002_checked

def cert1 : AnchoredWallDirectionCertificate :=
  .split (1/8) (regime003) (.split (1/4) (regime004) (regime005))
theorem cert1_checked : cert1.Check 3 1 points 0 1 := by
  unfold cert1
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime003_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime004_checked
    · exact regime005_checked

def cert2 : AnchoredWallDirectionCertificate :=
  .split (3/8) (.split (1/8) (regime006) (.split (1/4) (regime007) (regime008))) (.split (7/16) (regime009) (.split (1755/2048) (regime010) (regime011)))
theorem cert2_checked : cert2.Check 3 2 points 0 1 := by
  unfold cert2
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime006_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact regime007_checked
      · exact regime008_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime009_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact regime010_checked
      · exact regime011_checked

def cert3 : AnchoredWallDirectionCertificate :=
  regime012
theorem cert3_checked : cert3.Check 3 3 points 0 1 := by
  unfold cert3
  exact regime012_checked

def certs : Fin 4 → AnchoredWallDirectionCertificate := ![cert0, cert1, cert2, cert3]
theorem certs_checked : ∀ k, (certs k).Check 3 k points 0 1 := by
  intro k
  fin_cases k
  all_goals first | exact cert0_checked | exact cert1_checked | exact cert2_checked | exact cert3_checked

theorem initial_points_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ points, OpenSquare q (realPoint p) :=
  anchored_symbolic_wall_owned_points certs 3 points certs_checked q hcell hcont hchart

theorem gate_point005_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP005) := by
  exact initial_points_owned q hcell hcont hchart ownedP005 (by simp [points])

theorem gate_point006_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP006) := by
  exact initial_points_owned q hcell hcont hchart ownedP006 (by simp [points])

theorem gate_point007_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP007) := by
  exact initial_points_owned q hcell hcont hchart ownedP007 (by simp [points])

theorem gate_point008_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP008) := by
  exact initial_points_owned q hcell hcont hchart ownedP008 (by simp [points])

theorem gate_point009_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP009) := by
  exact initial_points_owned q hcell hcont hchart ownedP009 (by simp [points])

theorem gate_point010_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP010) := by
  exact initial_points_owned q hcell hcont hchart ownedP010 (by simp [points])

theorem gate_point011_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP011) := by
  exact initial_points_owned q hcell hcont hchart ownedP011 (by simp [points])

/-- Strict ownership of opposite cell 12 gate point 5, by half-turn. -/
theorem mirror_cell12_gate005_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP12_005) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 3 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP12_005)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP12_005 (by simp [points])
    simpa only [← mirrorP12_005_eq] using ho
  exact point_owned_of_halfTurn 3 originalP12_005 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 12 gate point 6, by half-turn. -/
theorem mirror_cell12_gate006_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP12_006) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 3 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP12_006)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP12_006 (by simp [points])
    simpa only [← mirrorP12_006_eq] using ho
  exact point_owned_of_halfTurn 3 originalP12_006 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 12 gate point 7, by half-turn. -/
theorem mirror_cell12_gate007_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP12_007) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 3 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP12_007)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP12_007 (by simp [points])
    simpa only [← mirrorP12_007_eq] using ho
  exact point_owned_of_halfTurn 3 originalP12_007 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 12 gate point 8, by half-turn. -/
theorem mirror_cell12_gate008_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP12_008) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 3 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP12_008)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP12_008 (by simp [points])
    simpa only [← mirrorP12_008_eq] using ho
  exact point_owned_of_halfTurn 3 originalP12_008 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 12 gate point 9, by half-turn. -/
theorem mirror_cell12_gate009_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP12_009) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 3 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP12_009)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP12_009 (by simp [points])
    simpa only [← mirrorP12_009_eq] using ho
  exact point_owned_of_halfTurn 3 originalP12_009 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 12 gate point 10, by half-turn. -/
theorem mirror_cell12_gate010_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP12_010) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 3 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP12_010)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP12_010 (by simp [points])
    simpa only [← mirrorP12_010_eq] using ho
  exact point_owned_of_halfTurn 3 originalP12_010 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 12 gate point 11, by half-turn. -/
theorem mirror_cell12_gate011_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP12_011) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 3 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP12_011)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP12_011 (by simp [points])
    simpa only [← mirrorP12_011_eq] using ho
  exact point_owned_of_halfTurn 3 originalP12_011 howned q
    (by simpa using hcell) hcont hchart

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
