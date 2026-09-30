import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairData
import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch00
import Mathlib.Tactic.NormNum

/-! Exact source-owned minus core vertex witnesses. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def terminal1CoreField : List QPoint := [(-356652443353215769622067279654861864053966244203/723781714267672898063120239769413334000000000000, 356382898733422334018115587002937399669206237547/723781714267672898063120239769413334000000000000), (-3853353047335590036401626645477178544584641/7821870646004311380566167416706000000000000, -367101997085198701329498807557560509/1971237561997054279376554288484375000000), (-356382898733422334018115587002937399669206237547/723781714267672898063120239769413334000000000000, -356652443353215769622067279654861864053966244203/723781714267672898063120239769413334000000000000), (367101997085198701329498807557560509/1971237561997054279376554288484375000000, -3853353047335590036401626645477178544584641/7821870646004311380566167416706000000000000), (356652443353215769622067279654861864053966244203/723781714267672898063120239769413334000000000000, -356382898733422334018115587002937399669206237547/723781714267672898063120239769413334000000000000), (3853353047335590036401626645477178544584641/7821870646004311380566167416706000000000000, 367101997085198701329498807557560509/1971237561997054279376554288484375000000), (356382898733422334018115587002937399669206237547/723781714267672898063120239769413334000000000000, 356652443353215769622067279654861864053966244203/723781714267672898063120239769413334000000000000), (-367101997085198701329498807557560509/1971237561997054279376554288484375000000, 3853353047335590036401626645477178544584641/7821870646004311380566167416706000000000000)]

theorem terminal1Triangle0_vertex_pairs :
    ∀ v ∈ terminal1Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal1CoreField := by
  intro v hv
  simp only [terminal1Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal1CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨@List.getElem_mem _ terminalPairOwner9 0 (by decide),
         @List.getElem_mem _ terminal1CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal1CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨@List.getElem_mem _ terminalPairOwner9 0 (by decide),
         @List.getElem_mem _ terminal1CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal1CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨@List.getElem_mem _ terminalPairOwner9 4 (by decide),
         @List.getElem_mem _ terminal1CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal1CoreField]

theorem terminal1Triangle1_vertex_pairs :
    ∀ v ∈ terminal1Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal1CoreField := by
  intro v hv
  simp only [terminal1Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal1CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨@List.getElem_mem _ terminalPairOwner13 0 (by decide),
         @List.getElem_mem _ terminal1CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal1CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨@List.getElem_mem _ terminalPairOwner13 0 (by decide),
         @List.getElem_mem _ terminal1CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal1CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨@List.getElem_mem _ terminalPairOwner13 1 (by decide),
         @List.getElem_mem _ terminal1CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal1CoreField]

end
end ElevenSquare.Tasks.T07
