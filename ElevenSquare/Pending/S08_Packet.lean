import ElevenSquare.Pending.S08_GapFunctions

/-! UNFINISHED FORMALIZATION OBLIGATIONS. See handoffs/S08_Packet.md.
Every `sorry` in this file is an explicit outstanding proof, not verified evidence. -/

namespace ElevenSquare.Pending
noncomputable section

def focusedRadii : Fin 33 → ℝ :=
  ![(18767167 / 10000000000), (4435327 / 2000000000), (5670363 / 2500000000), (1636033 / 1000000000), (6880181 / 5000000000), (1764113 / 1000000000), (8962451 / 10000000000), (5212397 / 5000000000), (5670363 / 2500000000), (1635053 / 1000000000), (10683139 / 10000000000), (1890121 / 1250000000), (4087019 / 2500000000), (13962901 / 10000000000), (20161291 / 10000000000), (12900283 / 10000000000), (534153 / 500000000), (1890121 / 1250000000), (678279 / 500000000), (4124329 / 5000000000), (35312013 / 10000000000), (11182451 / 10000000000), (3232837 / 5000000000), (8824483 / 2500000000), (9356857 / 10000000000), (8671199 / 10000000000), (7549783 / 5000000000), (293551 / 400000000), (10335557 / 10000000000), (40352153 / 10000000000), (1920157 / 2500000000), (8222903 / 2500000000), (67647473 / 10000000000)]

structure LocalPacket where
  radii : Fin 33 → ℝ
  maxRadius : ℝ
  representative : Fin 128 → Fin 42 → Gap
  aliases : Fin 128 → Fin 42 → List Gap
  curvature : Fin 128 → Fin 42 → ℚ
  dual : Fin 128 → Fin 33 → Fin 2 → Fin 42 → ℚ
  residual : Fin 128 → Fin 33 → Fin 2 → ℚ

def dualSign (s : Fin 2) : ℝ := (![(-1 : ℝ), 1] : Fin 2 → ℝ) s

def BranchCover (S : ℝ) (q₀ : Owner → UnitSquare) (p : LocalPacket) : Prop :=
  ∀ h, InRectangle p.radii h → LocalFeasible S q₀ h →
    ∃ b : Fin 128, ∀ i : Fin 42, ∃ g ∈ p.aliases b i, 0 ≤ gapValue S q₀ g h

def RowsTied (S : ℝ) (q₀ : Owner → UnitSquare) (p : LocalPacket) : Prop :=
  ∀ b i, p.representative b i ∈ p.aliases b i ∧
    ∀ g ∈ p.aliases b i, gapValue S q₀ g 0 = 0 ∧
      gapGradient S q₀ g = gapGradient S q₀ (p.representative b i)

def RowsTaylorBound (S : ℝ) (q₀ : Owner → UnitSquare) (p : LocalPacket) : Prop :=
  ∀ b i g, g ∈ p.aliases b i → ∀ h, InRectangle p.radii h →
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
    |gapValue S q₀ g (τ • h) - gapValue S q₀ g 0 -
      τ*LinearForm (gapGradient S q₀ (p.representative b i)) h| ≤
      τ^2*(p.curvature b i : ℝ)/2

def DualBounds (S : ℝ) (q₀ : Owner → UnitSquare) (p : LocalPacket) : Prop :=
  (∀ j, 0 < p.radii j ∧ p.radii j ≤ p.maxRadius ∧ p.radii j ≤ 1/64) ∧
  (0 ≤ p.maxRadius) ∧
  (∀ b i, 0 ≤ p.curvature b i) ∧
  (∀ b j s i, 0 ≤ p.dual b j s i) ∧
  (∀ b j s, 0 ≤ p.residual b j s) ∧
  (∀ b j s,
    (∑ k, |(∑ i, (p.dual b j s i : ℝ)*gapGradient S q₀ (p.representative b i) k)-
      (if k=j then dualSign s else 0)|) ≤ (p.residual b j s : ℝ)) ∧
  (∀ b j s, (∑ i, (p.dual b j s i : ℝ)*(p.curvature b i : ℝ)) <
    2*(p.radii j-(p.residual b j s : ℝ)*p.maxRadius))


end
end ElevenSquare.Pending
