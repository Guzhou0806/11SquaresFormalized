import ElevenSquare.Pending.S05_ResidualCover

/-!
A small trusted interface for externally generated polygon-union certificates.
Each leaf carries a Lean proof of a closed rational polygon inclusion.  At an
internal node, the old polygon is split by an exact rational halfplane; both
branches retain equality on the split line.  A generator may choose the tree,
but only these checked geometric facts can close it.
-/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

inductive PolygonCoverCert (regions : List Polygon) : Polygon → Prop
  | leaf (P K : Polygon) (hK : K ∈ regions)
      (hsub : P.carrier ⊆ K.carrier) : PolygonCoverCert regions P
  | split (P : Polygon) (l : Halfplane)
      (hle : PolygonCoverCert regions (l :: P))
      (hge : PolygonCoverCert regions
        ((⟨-l.a, -l.b, -l.c⟩ : Halfplane) :: P)) :
      PolygonCoverCert regions P

theorem PolygonCoverCert.sound {regions : List Polygon} {P : Polygon}
    (h : PolygonCoverCert regions P) :
    P.carrier ⊆ ⋃ K ∈ regions, Polygon.carrier K := by
  induction h with
  | leaf _ K hK hsub =>
    intro p hp
    exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK, hsub hp⟩⟩
  | split P l _ _ ihle ihge =>
    intro p hp
    rw [polygon_closed_split] at hp
    rcases hp with hleft | hright
    · exact ihle hleft
    · exact ihge hright

/-- A finite coverage certificate may be reused under any stronger input
polygon, without regenerating its subdivision. -/
theorem PolygonCoverCert.sound_of_subset {regions : List Polygon} {P : Polygon}
    (h : PolygonCoverCert regions P) {Q : Polygon}
    (hQP : Q.carrier ⊆ P.carrier) :
    Q.carrier ⊆ ⋃ K ∈ regions, Polygon.carrier K :=
  Set.Subset.trans hQP h.sound

end
end ElevenSquare.Tasks.T07
