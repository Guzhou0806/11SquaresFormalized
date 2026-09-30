import ElevenSquare.Tasks.T01.Handoff.Groups.G070.SymbolicRootShared

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots
noncomputable section

/-- Six fixed Voronoi facets bounding the first owner's source center region.
They are present in every initial slab row of physical cell five. -/
def source : Polygon :=
  [baselineBisector (5 : Fin 16) (0 : Fin 16),
   baselineBisector (5 : Fin 16) (1 : Fin 16),
   baselineBisector (5 : Fin 16) (2 : Fin 16),
   baselineBisector (5 : Fin 16) (6 : Fin 16),
   baselineBisector (5 : Fin 16) (9 : Fin 16),
   baselineBisector (5 : Fin 16) (4 : Fin 16)]

def sourceLiteral : Polygon :=
  [⟨(-532329/1000000 : ℚ), (-360029/1000000 : ℚ), (-52085762485336878091356109186263/50000000000000000000000000000000 : ℚ)⟩,
   ⟨(4093/1000000 : ℚ), (-26743/50000 : ℚ), (-8588608573212199176944164507707/16000000000000000000000000000000 : ℚ)⟩,
   ⟨(131233/250000 : ℚ), (-174177/500000 : ℚ), (62068170967257980456895308302299/100000000000000000000000000000000 : ℚ)⟩,
   ⟨(528203/1000000 : ℚ), (206179/1000000 : ℚ), (67405583643691805407653845828833/50000000000000000000000000000000 : ℚ)⟩,
   ⟨(-513/40000 : ℚ), (542089/1000000 : ℚ), (47524092848234315447117031328833/50000000000000000000000000000000 : ℚ)⟩,
   ⟨(-53613/100000 : ℚ), (43723/250000 : ℚ), (-18345863850780390140829354545289/50000000000000000000000000000000 : ℚ)⟩]

theorem source_eq_literal : source = sourceLiteral := by
  have hs0 : baselineRationalSite (0 : Fin 16) =
      ((104991/1000000 : ℚ), (265837/2000000 : ℚ)) := by rfl
  have hs1 : baselineRationalSite (1 : Fin 16) =
      ((186601/500000 : ℚ), (45503/1000000 : ℚ)) := by rfl
  have hs2 : baselineRationalSite (2 : Fin 16) =
      ((1267243/2000000 : ℚ), (34689/250000 : ℚ)) := by rfl
  have hs4 : baselineRationalSite (4 : Fin 16) =
      ((206181/2000000 : ℚ), (400379/1000000 : ℚ)) := by rfl
  have hs5 : baselineRationalSite (5 : Fin 16) =
      ((742311/2000000 : ℚ), (312933/1000000 : ℚ)) := by rfl
  have hs6 : baselineRationalSite (6 : Fin 16) =
      ((635257/1000000 : ℚ), (166409/400000 : ℚ)) := by rfl
  have hs9 : baselineRationalSite (9 : Fin 16) =
      ((364743/1000000 : ℚ), (233591/400000 : ℚ)) := by rfl
  simp only [source, sourceLiteral, baselineBisector,
    hs0, hs1, hs2, hs4, hs5, hs6, hs9]
  norm_num [baselineRationalCap]

theorem source_contains_of_slab (margin : ℚ) (p : Point)
    (hp : p ∈ (baselineSlab (5 : Fin 16) margin).carrier) :
    p ∈ source.carrier := by
  intro f hf
  have hbis (j : Fin 16) :
      baselineBisector (5 : Fin 16) j ∈ baselineSlab (5 : Fin 16) margin := by
    unfold baselineSlab baselineCellPolygon
    apply List.mem_append.mpr
    right
    apply List.mem_append.mpr
    right
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact hp _ (hbis _)

theorem source_contains_of_root_row (k : Fin 32) (p : Point)
    (hp : p ∈ (slabRow 32 (5 : Fin 16) k).centers.carrier) :
    p ∈ source.carrier := by
  exact source_contains_of_slab (slabMargin 32 k) p hp

theorem literal_contains_of_root_row (k : Fin 32) (p : Point)
    (hp : p ∈ (slabRow 32 (5 : Fin 16) k).centers.carrier) :
    p ∈ sourceLiteral.carrier := by
  rw [← source_eq_literal]
  exact source_contains_of_root_row k p hp

#print axioms source_contains_of_root_row
#print axioms literal_contains_of_root_row

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full
