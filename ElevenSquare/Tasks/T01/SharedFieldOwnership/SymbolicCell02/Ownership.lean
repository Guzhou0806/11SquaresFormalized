import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime000
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime001
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime002
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime003
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime004
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime005
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime006
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime007
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime008
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime009
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime010
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Regime011

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def cert0 : AnchoredWallDirectionCertificate :=
  .split (1/4) (.split (3/16) (regime000) (regime001)) (.split (7/16) (regime002) (regime003))
theorem cert0_checked : cert0.Check 2 0 points 0 1 := by
  unfold cert0
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime000_checked
    · exact regime001_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime002_checked
    · exact regime003_checked

def cert1 : AnchoredWallDirectionCertificate :=
  .split (711/4096) (regime004) (.split (1/2) (regime005) (regime006))
theorem cert1_checked : cert1.Check 2 1 points 0 1 := by
  unfold cert1
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime004_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime005_checked
    · exact regime006_checked

def cert2 : AnchoredWallDirectionCertificate :=
  .split (7/8) (regime007) (regime008)
theorem cert2_checked : cert2.Check 2 2 points 0 1 := by
  unfold cert2
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime007_checked
  · exact regime008_checked

def cert3 : AnchoredWallDirectionCertificate :=
  .split (1/2) (regime009) (.split (3/4) (regime010) (regime011))
theorem cert3_checked : cert3.Check 2 3 points 0 1 := by
  unfold cert3
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime009_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime010_checked
    · exact regime011_checked

def certs : Fin 4 → AnchoredWallDirectionCertificate := ![cert0, cert1, cert2, cert3]
theorem certs_checked : ∀ k, (certs k).Check 2 k points 0 1 := by
  intro k
  fin_cases k
  all_goals first | exact cert0_checked | exact cert1_checked | exact cert2_checked | exact cert3_checked

theorem initial_points_owned (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ points, OpenSquare q (realPoint p) :=
  anchored_symbolic_wall_owned_points certs 2 points certs_checked q hcell hcont hchart

theorem gate_point005_owned (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP005) := by
  exact initial_points_owned q hcell hcont hchart ownedP005 (by simp [points])

theorem gate_point006_owned (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP006) := by
  exact initial_points_owned q hcell hcont hchart ownedP006 (by simp [points])

theorem gate_point007_owned (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP007) := by
  exact initial_points_owned q hcell hcont hchart ownedP007 (by simp [points])

theorem gate_point008_owned (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP008) := by
  exact initial_points_owned q hcell hcont hchart ownedP008 (by simp [points])

theorem gate_point009_owned (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP009) := by
  exact initial_points_owned q hcell hcont hchart ownedP009 (by simp [points])

/-- Strict ownership of opposite cell 13 gate point 5, by half-turn. -/
theorem mirror_cell13_gate005_owned (q : UnitSquare)
    (hcell : ClosedCell 13 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP13_005) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 2 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP13_005)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP13_005 (by simp [points])
    simpa only [← mirrorP13_005_eq] using ho
  exact point_owned_of_halfTurn 2 originalP13_005 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 13 gate point 6, by half-turn. -/
theorem mirror_cell13_gate006_owned (q : UnitSquare)
    (hcell : ClosedCell 13 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP13_006) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 2 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP13_006)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP13_006 (by simp [points])
    simpa only [← mirrorP13_006_eq] using ho
  exact point_owned_of_halfTurn 2 originalP13_006 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 13 gate point 7, by half-turn. -/
theorem mirror_cell13_gate007_owned (q : UnitSquare)
    (hcell : ClosedCell 13 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP13_007) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 2 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP13_007)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP13_007 (by simp [points])
    simpa only [← mirrorP13_007_eq] using ho
  exact point_owned_of_halfTurn 2 originalP13_007 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 13 gate point 10, by half-turn. -/
theorem mirror_cell13_gate010_owned (q : UnitSquare)
    (hcell : ClosedCell 13 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP13_010) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 2 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP13_010)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP13_010 (by simp [points])
    simpa only [← mirrorP13_010_eq] using ho
  exact point_owned_of_halfTurn 2 originalP13_010 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 13 gate point 11, by half-turn. -/
theorem mirror_cell13_gate011_owned (q : UnitSquare)
    (hcell : ClosedCell 13 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP13_011) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 2 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP13_011)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP13_011 (by simp [points])
    simpa only [← mirrorP13_011_eq] using ho
  exact point_owned_of_halfTurn 2 originalP13_011 howned q
    (by simpa using hcell) hcont hchart

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
