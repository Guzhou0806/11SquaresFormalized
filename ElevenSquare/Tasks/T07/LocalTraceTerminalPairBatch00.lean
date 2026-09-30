import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairData
import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch00
import Mathlib.Tactic.NormNum

/-! Exact source-owned minus core vertex witnesses. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def terminal0CoreField : List QPoint := [(-381999999999612291640997718582269/775416718004562835462000000000000, 96221460097902340669121991935792747941891/195367891412608802099801927674000000000000), (-367101997085198701329498807557560509/745175466002384884878982000000000000, -367101997085198701329498807557560509/5913712498194926446399601152000000000000), (-96221460097902340669121991935792747941891/195367891412608802099801927674000000000000, -381999999999612291640997718582269/775416718004562835462000000000000), (367101997085198701329498807557560509/5913712498194926446399601152000000000000, -367101997085198701329498807557560509/745175466002384884878982000000000000), (381999999999612291640997718582269/775416718004562835462000000000000, -96221460097902340669121991935792747941891/195367891412608802099801927674000000000000), (367101997085198701329498807557560509/745175466002384884878982000000000000, 367101997085198701329498807557560509/5913712498194926446399601152000000000000), (96221460097902340669121991935792747941891/195367891412608802099801927674000000000000, 381999999999612291640997718582269/775416718004562835462000000000000), (-367101997085198701329498807557560509/5913712498194926446399601152000000000000, 367101997085198701329498807557560509/745175466002384884878982000000000000)]

theorem terminal0Triangle0_vertex_pairs :
    ∀ v ∈ terminal0Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal0CoreField := by
  intro v hv
  simp only [terminal0Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal0CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal0CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal0CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal0CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal0CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal0CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal0CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal0CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal0CoreField]

theorem terminal0Triangle1_vertex_pairs :
    ∀ v ∈ terminal0Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal0CoreField := by
  intro v hv
  simp only [terminal0Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal0CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal0CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal0CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal0CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal0CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal0CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal0CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal0CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal0CoreField]

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
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal1CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal1CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal1CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal1CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal1CoreField 4 (by decide)⟩
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
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal1CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal1CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal1CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal1CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal1CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal1CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal1CoreField]

def terminal2CoreField : List QPoint := [(-60646188604651025554283570752426597216163330051/123042905100396032471358442725802256240000000000, 60569817625405023066500950058625782833545330691/123042905100396032471358442725802256240000000000), (-2312011681560555187761495455486784103726581/4693122685672773229293654401616400000000000, -367101997085198701329498807557560509/1182742612316727124317957258471875000000), (-60569817625405023066500950058625782833545330691/123042905100396032471358442725802256240000000000, -60646188604651025554283570752426597216163330051/123042905100396032471358442725802256240000000000), (367101997085198701329498807557560509/1182742612316727124317957258471875000000, -2312011681560555187761495455486784103726581/4693122685672773229293654401616400000000000), (60646188604651025554283570752426597216163330051/123042905100396032471358442725802256240000000000, -60569817625405023066500950058625782833545330691/123042905100396032471358442725802256240000000000), (2312011681560555187761495455486784103726581/4693122685672773229293654401616400000000000, 367101997085198701329498807557560509/1182742612316727124317957258471875000000), (60569817625405023066500950058625782833545330691/123042905100396032471358442725802256240000000000, 60646188604651025554283570752426597216163330051/123042905100396032471358442725802256240000000000), (-367101997085198701329498807557560509/1182742612316727124317957258471875000000, 2312011681560555187761495455486784103726581/4693122685672773229293654401616400000000000)]

theorem terminal2Triangle0_vertex_pairs :
    ∀ v ∈ terminal2Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal2CoreField := by
  intro v hv
  simp only [terminal2Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal2CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal2CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal2CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal2CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal2CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal2CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal2CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal2CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal2CoreField]

theorem terminal2Triangle1_vertex_pairs :
    ∀ v ∈ terminal2Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal2CoreField := by
  intro v hv
  simp only [terminal2Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal2CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal2CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal2CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal2CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal2CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal2CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal2CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal2CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal2CoreField]

def terminal3CoreField : List QPoint := [(-1213229236848144587056250100102381025186231703407/2460858531790260035377510468390106231600000000000, 1211090849259489605398509024474032580371470061423/2460858531790260035377510468390106231600000000000), (-5780028653248392341605686644468748922975689/11732807831945132076811463322514000000000000, -2569713979596390909306491652902923563/5913713624972344796779971432718750000000), (-1211090849259489605398509024474032580371470061423/2460858531790260035377510468390106231600000000000, -1213229236848144587056250100102381025186231703407/2460858531790260035377510468390106231600000000000), (2569713979596390909306491652902923563/5913713624972344796779971432718750000000, -5780028653248392341605686644468748922975689/11732807831945132076811463322514000000000000), (1213229236848144587056250100102381025186231703407/2460858531790260035377510468390106231600000000000, -1211090849259489605398509024474032580371470061423/2460858531790260035377510468390106231600000000000), (5780028653248392341605686644468748922975689/11732807831945132076811463322514000000000000, 2569713979596390909306491652902923563/5913713624972344796779971432718750000000), (1211090849259489605398509024474032580371470061423/2460858531790260035377510468390106231600000000000, 1213229236848144587056250100102381025186231703407/2460858531790260035377510468390106231600000000000), (-2569713979596390909306491652902923563/5913713624972344796779971432718750000000, 5780028653248392341605686644468748922975689/11732807831945132076811463322514000000000000)]

theorem terminal3Triangle0_vertex_pairs :
    ∀ v ∈ terminal3Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal3CoreField := by
  intro v hv
  simp only [terminal3Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal3CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal3CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal3CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal3CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal3CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal3CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal3CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal3CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal3CoreField]

theorem terminal3Triangle1_vertex_pairs :
    ∀ v ∈ terminal3Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal3CoreField := by
  intro v hv
  simp only [terminal3Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal3CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal3CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal3CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal3CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal3CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal3CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal3CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal3CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal3CoreField]

def terminal4CoreField : List QPoint := [(-379229594279808929445854777707851041088018970867/769018474330358422896357593048719078000000000000, 378370420599587593458466444993592152971446591731/769018474330358422896357593048719078000000000000), (-1926675973014799390402761328490377935951557/3910936440765354693860411026826000000000000, -1101305991255596103988496422672681527/1971238125385763454566739428843750000000), (-378370420599587593458466444993592152971446591731/769018474330358422896357593048719078000000000000, -379229594279808929445854777707851041088018970867/769018474330358422896357593048719078000000000000), (1101305991255596103988496422672681527/1971238125385763454566739428843750000000, -1926675973014799390402761328490377935951557/3910936440765354693860411026826000000000000), (379229594279808929445854777707851041088018970867/769018474330358422896357593048719078000000000000, -378370420599587593458466444993592152971446591731/769018474330358422896357593048719078000000000000), (1926675973014799390402761328490377935951557/3910936440765354693860411026826000000000000, 1101305991255596103988496422672681527/1971238125385763454566739428843750000000), (378370420599587593458466444993592152971446591731/769018474330358422896357593048719078000000000000, 379229594279808929445854777707851041088018970867/769018474330358422896357593048719078000000000000), (-1101305991255596103988496422672681527/1971238125385763454566739428843750000000, 1926675973014799390402761328490377935951557/3910936440765354693860411026826000000000000)]

theorem terminal4Triangle0_vertex_pairs :
    ∀ v ∈ terminal4Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal4CoreField := by
  intro v hv
  simp only [terminal4Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal4CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal4CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal4CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal4CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal4CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal4CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal4CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal4CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal4CoreField]

theorem terminal4Triangle1_vertex_pairs :
    ∀ v ∈ terminal4Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal4CoreField := by
  intro v hv
  simp only [terminal4Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal4CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal4CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal4CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal4CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal4CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal4CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal4CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal4CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal4CoreField]

def terminal5CoreField : List QPoint := [(-6069200833319139338985487354289025535813185004403/12304299301043186165516833355687914214000000000000, 6052399212282710695678996826989300182289122368371/12304299301043186165516833355687914214000000000000), (-11560054002578810916423061323448229827906797/23465622370469458175086890555866000000000000, -367101997085198701329498807557560509/537610483194406574759138804890625000000), (-6052399212282710695678996826989300182289122368371/12304299301043186165516833355687914214000000000000, -6069200833319139338985487354289025535813185004403/12304299301043186165516833355687914214000000000000), (367101997085198701329498807557560509/537610483194406574759138804890625000000, -11560054002578810916423061323448229827906797/23465622370469458175086890555866000000000000), (6069200833319139338985487354289025535813185004403/12304299301043186165516833355687914214000000000000, -6052399212282710695678996826989300182289122368371/12304299301043186165516833355687914214000000000000), (11560054002578810916423061323448229827906797/23465622370469458175086890555866000000000000, 367101997085198701329498807557560509/537610483194406574759138804890625000000), (6052399212282710695678996826989300182289122368371/12304299301043186165516833355687914214000000000000, 6069200833319139338985487354289025535813185004403/12304299301043186165516833355687914214000000000000), (-367101997085198701329498807557560509/537610483194406574759138804890625000000, 11560054002578810916423061323448229827906797/23465622370469458175086890555866000000000000)]

theorem terminal5Triangle0_vertex_pairs :
    ∀ v ∈ terminal5Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal5CoreField := by
  intro v hv
  simp only [terminal5Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal5CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal5CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal5CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal5CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal5CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal5CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal5CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal5CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal5CoreField]

theorem terminal5Triangle1_vertex_pairs :
    ∀ v ∈ terminal5Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal5CoreField := by
  intro v hv
  simp only [terminal5Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal5CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal5CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal5CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal5CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal5CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal5CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal5CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal5CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal5CoreField]

def terminal6CoreField : List QPoint := [(-1517682039728163160709133930306841361282558994899/3076075948556001991109074505832182182000000000000, 1512717923554921735005823527352607458047875232211/3076075948556001991109074505832182182000000000000), (-11560051799966828405230853346455384482543743/23465626841522254189396199829758000000000000, -367101997085198701329498807557560509/454901264762760820979299779578125000000), (-1512717923554921735005823527352607458047875232211/3076075948556001991109074505832182182000000000000, -1517682039728163160709133930306841361282558994899/3076075948556001991109074505832182182000000000000), (367101997085198701329498807557560509/454901264762760820979299779578125000000, -11560051799966828405230853346455384482543743/23465626841522254189396199829758000000000000), (1517682039728163160709133930306841361282558994899/3076075948556001991109074505832182182000000000000, -1512717923554921735005823527352607458047875232211/3076075948556001991109074505832182182000000000000), (11560051799966828405230853346455384482543743/23465626841522254189396199829758000000000000, 367101997085198701329498807557560509/454901264762760820979299779578125000000), (1512717923554921735005823527352607458047875232211/3076075948556001991109074505832182182000000000000, 1517682039728163160709133930306841361282558994899/3076075948556001991109074505832182182000000000000), (-367101997085198701329498807557560509/454901264762760820979299779578125000000, 11560051799966828405230853346455384482543743/23465626841522254189396199829758000000000000)]

theorem terminal6Triangle0_vertex_pairs :
    ∀ v ∈ terminal6Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal6CoreField := by
  intro v hv
  simp only [terminal6Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal6CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal6CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal6CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal6CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal6CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal6CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal6CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal6CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal6CoreField]

theorem terminal6Triangle1_vertex_pairs :
    ∀ v ∈ terminal6Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal6CoreField := by
  intro v hv
  simp only [terminal6Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal6CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal6CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal6CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal6CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal6CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal6CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal6CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal6CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal6CoreField]

def terminal7CoreField : List QPoint := [(-10205471404038296495271721124682138711870429601/20679511040048114610299922706532981200000000000, 71168755003042410216100033766419477500770790247/144756577280336802272099458945730868400000000000), (-192667487170880813480665733999395526327003/391093867629175270101506566377200000000000, -367101997085198701329498807557560509/394247850432636360989421941912500000000), (-71168755003042410216100033766419477500770790247/144756577280336802272099458945730868400000000000, -10205471404038296495271721124682138711870429601/20679511040048114610299922706532981200000000000), (367101997085198701329498807557560509/394247850432636360989421941912500000000, -192667487170880813480665733999395526327003/391093867629175270101506566377200000000000), (10205471404038296495271721124682138711870429601/20679511040048114610299922706532981200000000000, -71168755003042410216100033766419477500770790247/144756577280336802272099458945730868400000000000), (192667487170880813480665733999395526327003/391093867629175270101506566377200000000000, 367101997085198701329498807557560509/394247850432636360989421941912500000000), (71168755003042410216100033766419477500770790247/144756577280336802272099458945730868400000000000, 10205471404038296495271721124682138711870429601/20679511040048114610299922706532981200000000000), (-367101997085198701329498807557560509/394247850432636360989421941912500000000, 192667487170880813480665733999395526327003/391093867629175270101506566377200000000000)]

theorem terminal7Triangle0_vertex_pairs :
    ∀ v ∈ terminal7Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal7CoreField := by
  intro v hv
  simp only [terminal7Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal7CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal7CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal7CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal7CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal7CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal7CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal7CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal7CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal7CoreField]

theorem terminal7Triangle1_vertex_pairs :
    ∀ v ∈ terminal7Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal7CoreField := by
  intro v hv
  simp only [terminal7Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal7CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal7CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal7CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal7CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal7CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal7CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal7CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal7CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal7CoreField]

def terminal8CoreField : List QPoint := [(-18980571290421273795424234251343079417292684871/38450984765179841630083025854938996400000000000, 18899427047667820152233659529374287821704447559/38450984765179841630083025854938996400000000000), (-2890011573359218031812583350993317779784027/5866409504788561056292368253622000000000000, -6240733950448377922601479728478528653/5913719258859436548681822836312500000000), (-18899427047667820152233659529374287821704447559/38450984765179841630083025854938996400000000000, -18980571290421273795424234251343079417292684871/38450984765179841630083025854938996400000000000), (6240733950448377922601479728478528653/5913719258859436548681822836312500000000, -2890011573359218031812583350993317779784027/5866409504788561056292368253622000000000000), (18980571290421273795424234251343079417292684871/38450984765179841630083025854938996400000000000, -18899427047667820152233659529374287821704447559/38450984765179841630083025854938996400000000000), (2890011573359218031812583350993317779784027/5866409504788561056292368253622000000000000, 6240733950448377922601479728478528653/5913719258859436548681822836312500000000), (18899427047667820152233659529374287821704447559/38450984765179841630083025854938996400000000000, 18980571290421273795424234251343079417292684871/38450984765179841630083025854938996400000000000), (-6240733950448377922601479728478528653/5913719258859436548681822836312500000000, 2890011573359218031812583350993317779784027/5866409504788561056292368253622000000000000)]

theorem terminal8Triangle0_vertex_pairs :
    ∀ v ∈ terminal8Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal8CoreField := by
  intro v hv
  simp only [terminal8Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal8CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal8CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal8CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal8CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal8CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal8CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal8CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal8CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal8CoreField]

theorem terminal8Triangle1_vertex_pairs :
    ∀ v ∈ terminal8Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal8CoreField := by
  intro v hv
  simp only [terminal8Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal8CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal8CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal8CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal8CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal8CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal8CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal8CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal8CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal8CoreField]

def terminal9CoreField : List QPoint := [(-357371184803173325316684176143785009510822233851/723783644841844015292284482803433974000000000000, 355664066709363586886014507329269205710852194043/723783644841844015292284482803433974000000000000), (-11560042989518898360462021438484003101091527/23465644725733438246633436925326000000000000, -6974937944618775325260477343593649671/5913720949025564074252378257390625000000), (-355664066709363586886014507329269205710852194043/723783644841844015292284482803433974000000000000, -357371184803173325316684176143785009510822233851/723783644841844015292284482803433974000000000000), (6974937944618775325260477343593649671/5913720949025564074252378257390625000000, -11560042989518898360462021438484003101091527/23465644725733438246633436925326000000000000), (357371184803173325316684176143785009510822233851/723783644841844015292284482803433974000000000000, -355664066709363586886014507329269205710852194043/723783644841844015292284482803433974000000000000), (11560042989518898360462021438484003101091527/23465644725733438246633436925326000000000000, 6974937944618775325260477343593649671/5913720949025564074252378257390625000000), (355664066709363586886014507329269205710852194043/723783644841844015292284482803433974000000000000, 357371184803173325316684176143785009510822233851/723783644841844015292284482803433974000000000000), (-6974937944618775325260477343593649671/5913720949025564074252378257390625000000, 11560042989518898360462021438484003101091527/23465644725733438246633436925326000000000000)]

theorem terminal9Triangle0_vertex_pairs :
    ∀ v ∈ terminal9Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal9CoreField := by
  intro v hv
  simp only [terminal9Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal9CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal9CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal9CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal9CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal9CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal9CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal9CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal9CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal9CoreField]

theorem terminal9Triangle1_vertex_pairs :
    ∀ v ∈ terminal9Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal9CoreField := by
  intro v hv
  simp only [terminal9Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal9CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal9CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal9CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal9CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal9CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal9CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal9CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal9CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal9CoreField]

end
end ElevenSquare.Tasks.T07
