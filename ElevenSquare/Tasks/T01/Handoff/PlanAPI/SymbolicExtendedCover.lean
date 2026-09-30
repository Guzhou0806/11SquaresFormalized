import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicEmpty3
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A moving BSP whose empty leaves carry an exact three-halfplane
infeasibility certificate. Other leaves reuse the original Farkas witnesses. -/
inductive SymbolicExtendedCoverCertificate where
  | hit (index : ℕ) (witnesses : List SymbolicFarkasWitness)
  | empty3 (witness : SymbolicEmpty3Witness)
  | split (facet : SymbolicFacet)
      (left right : SymbolicExtendedCoverCertificate)

def SymbolicExtendedCoverCertificate.Check
    (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ) :
    SymbolicExtendedCoverCertificate → Prop
  | .hit index witnesses =>
      index < targets.length ∧
        SymbolicPolygonImplicationCheck source (targets.getD index [])
          witnesses l u
  | .empty3 witness => witness.Check source l u
  | .split facet left right =>
      left.Check (facet :: source) targets l u ∧
        right.Check (facet.flip :: source) targets l u

instance symbolicExtendedCoverCheckDecidable (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ)
    (cover : SymbolicExtendedCoverCertificate) :
    Decidable (cover.Check source targets l u) := by
  induction cover generalizing source with
  | hit index ws =>
      change Decidable (index < targets.length ∧
        SymbolicPolygonImplicationCheck source (targets.getD index []) ws l u)
      infer_instance
  | empty3 witness =>
      change Decidable (witness.Check source l u)
      infer_instance
  | split facet left right ihl ihr =>
      change Decidable
        (left.Check (facet :: source) targets l u ∧
         right.Check (facet.flip :: source) targets l u)
      letI := ihl (facet :: source)
      letI := ihr (facet.flip :: source)
      infer_instance

theorem symbolic_extended_cover_sound (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ)
    (cover : SymbolicExtendedCoverCertificate)
    (hc : cover.Check source targets l u)
    (t : ℝ) (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (x : Point) (hx : SymbolicPolygonContains source t x) :
    ∃ target ∈ targets, SymbolicPolygonContains target t x := by
  induction cover generalizing source with
  | hit index ws =>
      refine ⟨targets.getD index [], ?_, ?_⟩
      · rw [List.getD_eq_getElem targets [] hc.1]
        exact List.get_mem ..
      · exact symbolic_polygon_implication_sound source
          (targets.getD index []) ws l u hc.2 t hlt htu x hx
  | empty3 witness =>
      exact False.elim (symbolic_empty3_sound witness source l u
        hc t hlt htu x hx)
  | split facet left right ihl ihr =>
      by_cases hfacet : facet.contains t x
      · apply ihl (facet :: source) hc.1
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hfacet
        · exact hx f hf
      · apply ihr (facet.flip :: source) hc.2
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact symbolic_facet_flip_contains facet t x hfacet
        · exact hx f hf

theorem symbolic_extended_wall_cover_for_square (q : UnitSquare)
    (cell : Fin 16) (t : ℝ) (l u : ℚ)
    (targets : List (List SymbolicFacet))
    (cover : SymbolicExtendedCoverCertificate)
    (hc : cover.Check (symbolicWallScaledSlab cell) targets l u)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell cell (normalizeCenter q.center)) :
    ∃ target ∈ targets, SymbolicPolygonContains target t q.center := by
  exact symbolic_extended_cover_sound (symbolicWallScaledSlab cell)
    targets l u cover hc t hlt htu q.center
    (symbolic_wall_scaled_slab_contains q cell t ha hcont hcell)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_extended_cover_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_extended_wall_cover_for_square
