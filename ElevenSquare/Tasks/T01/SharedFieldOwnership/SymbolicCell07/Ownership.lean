import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime000
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime001
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime002
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime003
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime004
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime005
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime006
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime007
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime008
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime009
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime010
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime011
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime012
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime013
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime014
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Regime015

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def cert0 : AnchoredWallDirectionCertificate :=
  .split (5/8) (.split (1/2) (regime000) (regime001)) (.split (3/4) (regime002) (regime003))
theorem cert0_checked : cert0.Check 7 0 points 0 1 := by
  unfold cert0
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime000_checked
    · exact regime001_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime002_checked
    · exact regime003_checked

def cert1 : AnchoredWallDirectionCertificate :=
  .split (1/4) (.split (3/16) (regime004) (regime005)) (.split (7/16) (regime006) (.split (1/2) (regime007) (regime008)))
theorem cert1_checked : cert1.Check 7 1 points 0 1 := by
  unfold cert1
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime004_checked
    · exact regime005_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime006_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact regime007_checked
      · exact regime008_checked

def cert2 : AnchoredWallDirectionCertificate :=
  .split (3/16) (regime009) (.split (1/4) (regime010) (regime011))
theorem cert2_checked : cert2.Check 7 2 points 0 1 := by
  unfold cert2
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact regime009_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime010_checked
    · exact regime011_checked

def cert3 : AnchoredWallDirectionCertificate :=
  .split (3/16) (.split (1/8) (regime012) (regime013)) (.split (1/4) (regime014) (regime015))
theorem cert3_checked : cert3.Check 7 3 points 0 1 := by
  unfold cert3
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime012_checked
    · exact regime013_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact regime014_checked
    · exact regime015_checked

def certs : Fin 4 → AnchoredWallDirectionCertificate := ![cert0, cert1, cert2, cert3]
theorem certs_checked : ∀ k, (certs k).Check 7 k points 0 1 := by
  intro k
  fin_cases k
  all_goals first | exact cert0_checked | exact cert1_checked | exact cert2_checked | exact cert3_checked

theorem initial_points_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ points, OpenSquare q (realPoint p) :=
  anchored_symbolic_wall_owned_points certs 7 points certs_checked q hcell hcont hchart

theorem gate_point006_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP006) := by
  exact initial_points_owned q hcell hcont hchart ownedP006 (by simp [points])

theorem gate_point007_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP007) := by
  exact initial_points_owned q hcell hcont hchart ownedP007 (by simp [points])

theorem gate_point008_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP008) := by
  exact initial_points_owned q hcell hcont hchart ownedP008 (by simp [points])

theorem gate_point009_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP009) := by
  exact initial_points_owned q hcell hcont hchart ownedP009 (by simp [points])

theorem gate_point010_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP010) := by
  exact initial_points_owned q hcell hcont hchart ownedP010 (by simp [points])

theorem gate_point011_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP011) := by
  exact initial_points_owned q hcell hcont hchart ownedP011 (by simp [points])

theorem gate_point012_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP012) := by
  exact initial_points_owned q hcell hcont hchart ownedP012 (by simp [points])

theorem gate_point013_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP013) := by
  exact initial_points_owned q hcell hcont hchart ownedP013 (by simp [points])

theorem gate_point014_owned (q : UnitSquare)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint ownedP014) := by
  exact initial_points_owned q hcell hcont hchart ownedP014 (by simp [points])

/-- Strict ownership of opposite cell 8 gate point 5, by half-turn. -/
theorem mirror_cell08_gate005_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_005) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_005)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_005 (by simp [points])
    simpa only [← mirrorP08_005_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_005 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 8 gate point 6, by half-turn. -/
theorem mirror_cell08_gate006_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_006) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_006)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_006 (by simp [points])
    simpa only [← mirrorP08_006_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_006 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 8 gate point 7, by half-turn. -/
theorem mirror_cell08_gate007_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_007) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_007)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_007 (by simp [points])
    simpa only [← mirrorP08_007_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_007 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 8 gate point 8, by half-turn. -/
theorem mirror_cell08_gate008_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_008) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_008)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_008 (by simp [points])
    simpa only [← mirrorP08_008_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_008 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 8 gate point 10, by half-turn. -/
theorem mirror_cell08_gate010_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_010) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_010)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_010 (by simp [points])
    simpa only [← mirrorP08_010_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_010 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 8 gate point 11, by half-turn. -/
theorem mirror_cell08_gate011_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_011) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_011)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_011 (by simp [points])
    simpa only [← mirrorP08_011_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_011 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 8 gate point 12, by half-turn. -/
theorem mirror_cell08_gate012_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_012) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_012)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_012 (by simp [points])
    simpa only [← mirrorP08_012_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_012 howned q
    (by simpa using hcell) hcont hchart

/-- Strict ownership of opposite cell 8 gate point 13, by half-turn. -/
theorem mirror_cell08_gate013_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint originalP08_013) := by
  have howned : ∀ q : UnitSquare,
      ClosedCell 7 (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint originalP08_013)) := by
    intro q hc ht hch
    have ho := initial_points_owned q hc ht hch mirrorP08_013 (by simp [points])
    simpa only [← mirrorP08_013_eq] using ho
  exact point_owned_of_halfTurn 7 originalP08_013 howned q
    (by simpa using hcell) hcont hchart

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
