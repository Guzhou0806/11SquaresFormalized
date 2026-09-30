import ElevenSquare.Tasks.T02.IntegerCoverBridge

namespace ElevenSquare.Tasks.T02.IntegerCover
noncomputable section

/-- Reconstruct candidate weights from at most two source indices. The output
still has to pass `Implication.Check`; negative or degenerate determinants do
not bypass any condition. No completeness claim is needed for this proposer. -/
def sparseImplication (hs : Poly) (h : Plane) : List ℕ → Implication
  | [] => ⟨1, []⟩
  | [i] =>
    let g := hs.getD i zero
    if g.a = 0 then ⟨g.b.natAbs, [(i, h.b.natAbs)]⟩
    else ⟨g.a.natAbs, [(i, h.a.natAbs)]⟩
  | [i, j] =>
    let g := hs.getD i zero
    let k := hs.getD j zero
    let d := g.a * k.b - g.b * k.a
    let u := h.a * k.b - h.b * k.a
    let v := g.a * h.b - g.b * h.a
    let sign : ℤ := if 0 ≤ d then 1 else -1
    ⟨d.natAbs, [(i, (sign * u).toNat), (j, (sign * v).toNat)]⟩
  | _ => ⟨0, []⟩

inductive SparseCertificate where
  | empty (w : Combination)
  | hit (index : ℕ) (supports : List (List ℕ))
  | split (h : Plane) (left right : SparseCertificate)

/-- Expand inside Lean, then use exactly the proved integer checker. Extra or
missing support entries cannot create an unsound implication: the expanded
polygon witness still passes the original target-length and leaf checks. -/
def SparseCertificate.expand (source : Poly) (targets : List Poly) :
    SparseCertificate → Certificate
  | .empty ws => .empty ws
  | .hit i supports => .hit i (((targets.getD i []).zip supports).map
      (fun hw => sparseImplication source hw.1 hw.2))
  | .split h l r => .split h (l.expand (h :: source) targets)
      (r.expand (flip h :: source) targets)

theorem sparse_certificate_sound (source : Poly) (targets : List Poly)
    (c : SparseCertificate) (hc : (c.expand source targets).Check source targets)
    (p : Point) (hp : p ∈ source.carrier) : ∃ t ∈ targets, p ∈ t.carrier :=
  certificate_sound source targets (c.expand source targets) hc p hp

end
end ElevenSquare.Tasks.T02.IntegerCover
