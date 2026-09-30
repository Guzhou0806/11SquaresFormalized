import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairData
import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch07
import Mathlib.Tactic.NormNum

/-! Exact source-owned minus core vertex witnesses. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def terminal250CoreField : List QPoint := [(-304799879935227759389335341633238147823275161863/617467158399943193106879456442410234800000000000, -303498051185957732671764875630081051606538663097/617467158399943193106879456442410234800000000000), (-6636472929425556022398568118006567067277/6294641526700786432471429031143600000000000, -49915083123214964016808187693253184529709/101322197612889922454268475350400000000000), (303498051185957732671764875630081051606538663097/617467158399943193106879456442410234800000000000, -304799879935227759389335341633238147823275161863/617467158399943193106879456442410234800000000000), (49915083123214964016808187693253184529709/101322197612889922454268475350400000000000, -6636472929425556022398568118006567067277/6294641526700786432471429031143600000000000), (304799879935227759389335341633238147823275161863/617467158399943193106879456442410234800000000000, 303498051185957732671764875630081051606538663097/617467158399943193106879456442410234800000000000), (6636472929425556022398568118006567067277/6294641526700786432471429031143600000000000, 49915083123214964016808187693253184529709/101322197612889922454268475350400000000000), (-303498051185957732671764875630081051606538663097/617467158399943193106879456442410234800000000000, 304799879935227759389335341633238147823275161863/617467158399943193106879456442410234800000000000), (-49915083123214964016808187693253184529709/101322197612889922454268475350400000000000, 6636472929425556022398568118006567067277/6294641526700786432471429031143600000000000)]

theorem terminal250Triangle0_vertex_pairs :
    ∀ v ∈ terminal250Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal250CoreField := by
  intro v hv
  simp only [terminal250Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal250CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal250CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal250CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal250CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal250CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal250CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal250CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal250CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal250CoreField]

theorem terminal250Triangle1_vertex_pairs :
    ∀ v ∈ terminal250Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal250CoreField := by
  intro v hv
  simp only [terminal250Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal250CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal250CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal250CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal250CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal250CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal250CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal250CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal250CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal250CoreField]

def terminal251CoreField : List QPoint := [(-952739698795659023180165529480527235021153467/1930555667020272249656482406614084880000000000, -949148742530922667797340009342917165972373637/1930555667020272249656482406614084880000000000), (-1792791265295055418373072903916465984999/1927415780186038725116083468954000000000000, -748914961718255518717214717809736343312477/1520215263245326318401417947344000000000000), (949148742530922667797340009342917165972373637/1930555667020272249656482406614084880000000000, -952739698795659023180165529480527235021153467/1930555667020272249656482406614084880000000000), (748914961718255518717214717809736343312477/1520215263245326318401417947344000000000000, -1792791265295055418373072903916465984999/1927415780186038725116083468954000000000000), (952739698795659023180165529480527235021153467/1930555667020272249656482406614084880000000000, 949148742530922667797340009342917165972373637/1930555667020272249656482406614084880000000000), (1792791265295055418373072903916465984999/1927415780186038725116083468954000000000000, 748914961718255518717214717809736343312477/1520215263245326318401417947344000000000000), (-949148742530922667797340009342917165972373637/1930555667020272249656482406614084880000000000, 952739698795659023180165529480527235021153467/1930555667020272249656482406614084880000000000), (-748914961718255518717214717809736343312477/1520215263245326318401417947344000000000000, 1792791265295055418373072903916465984999/1927415780186038725116083468954000000000000)]

theorem terminal251Triangle0_vertex_pairs :
    ∀ v ∈ terminal251Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal251CoreField := by
  intro v hv
  simp only [terminal251Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal251CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal251CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal251CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal251CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal251CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal251CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal251CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal251CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal251CoreField]

theorem terminal251Triangle1_vertex_pairs :
    ∀ v ∈ terminal251Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal251CoreField := by
  intro v hv
  simp only [terminal251Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal251CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal251CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal251CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal251CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal251CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal251CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal251CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal251CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal251CoreField]

def terminal252CoreField : List QPoint := [(-31117706878118291290393608656825087335657018283/63070267851535712214440302268783542000000000000, -31016046902066838469510077662073853045225679381/63070267851535712214440302268783542000000000000), (-49726368253183905551716285282314609162867/61692819293509143917690066292326000000000000, -749103676588286577182306620220674918679319/1520597658642831012055741070585500000000000), (31016046902066838469510077662073853045225679381/63070267851535712214440302268783542000000000000, -31117706878118291290393608656825087335657018283/63070267851535712214440302268783542000000000000), (749103676588286577182306620220674918679319/1520597658642831012055741070585500000000000, -49726368253183905551716285282314609162867/61692819293509143917690066292326000000000000), (31117706878118291290393608656825087335657018283/63070267851535712214440302268783542000000000000, 31016046902066838469510077662073853045225679381/63070267851535712214440302268783542000000000000), (49726368253183905551716285282314609162867/61692819293509143917690066292326000000000000, 749103676588286577182306620220674918679319/1520597658642831012055741070585500000000000), (-31016046902066838469510077662073853045225679381/63070267851535712214440302268783542000000000000, 31117706878118291290393608656825087335657018283/63070267851535712214440302268783542000000000000), (-749103676588286577182306620220674918679319/1520597658642831012055741070585500000000000, 49726368253183905551716285282314609162867/61692819293509143917690066292326000000000000)]

theorem terminal252Triangle0_vertex_pairs :
    ∀ v ∈ terminal252Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal252CoreField := by
  intro v hv
  simp only [terminal252Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal252CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal252CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal252CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal252CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal252CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal252CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal252CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal252CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal252CoreField]

theorem terminal252Triangle1_vertex_pairs :
    ∀ v ∈ terminal252Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal252CoreField := by
  intro v hv
  simp only [terminal252Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal252CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal252CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal252CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal252CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal252CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal252CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal252CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal252CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal252CoreField]

def terminal253CoreField : List QPoint := [(-381287939116931560342454090683207212793141310107/772999491193398158066436151071661606000000000000, -380233796650907762237338009844895130597327022501/772999491193398158066436151071661606000000000000), (-687331009131453439608890564373447915266371/1007902846322365160180223013987078000000000000, -249764130486105878549132840877204498015387/506993383461954305925665499993500000000000), (380233796650907762237338009844895130597327022501/772999491193398158066436151071661606000000000000, -381287939116931560342454090683207212793141310107/772999491193398158066436151071661606000000000000), (249764130486105878549132840877204498015387/506993383461954305925665499993500000000000, -687331009131453439608890564373447915266371/1007902846322365160180223013987078000000000000), (381287939116931560342454090683207212793141310107/772999491193398158066436151071661606000000000000, 380233796650907762237338009844895130597327022501/772999491193398158066436151071661606000000000000), (687331009131453439608890564373447915266371/1007902846322365160180223013987078000000000000, 249764130486105878549132840877204498015387/506993383461954305925665499993500000000000), (-380233796650907762237338009844895130597327022501/772999491193398158066436151071661606000000000000, 381287939116931560342454090683207212793141310107/772999491193398158066436151071661606000000000000), (-249764130486105878549132840877204498015387/506993383461954305925665499993500000000000, 687331009131453439608890564373447915266371/1007902846322365160180223013987078000000000000)]

theorem terminal253Triangle0_vertex_pairs :
    ∀ v ∈ terminal253Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal253CoreField := by
  intro v hv
  simp only [terminal253Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal253CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal253CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal253CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal253CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal253CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal253CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal253CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal253CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal253CoreField]

theorem terminal253Triangle1_vertex_pairs :
    ∀ v ∈ terminal253Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal253CoreField := by
  intro v hv
  simp only [terminal253Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal253CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal253CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal253CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal253CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal253CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal253CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal253CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal253CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal253CoreField]

def terminal254CoreField : List QPoint := [(-89737404489421741500583954326701515132065886363/181973740451351294722914594604383574000000000000, -89534391380883927547388057017227731425433204773/181973740451351294722914594604383574000000000000), (-843649826473846868193349728100901177467161/1512234562043575503351793130115826000000000000, -749481106328348694112490425042552069413003/1521362738474422035565184235529000000000000), (89534391380883927547388057017227731425433204773/181973740451351294722914594604383574000000000000, -89737404489421741500583954326701515132065886363/181973740451351294722914594604383574000000000000), (749481106328348694112490425042552069413003/1521362738474422035565184235529000000000000, -843649826473846868193349728100901177467161/1512234562043575503351793130115826000000000000), (89737404489421741500583954326701515132065886363/181973740451351294722914594604383574000000000000, 89534391380883927547388057017227731425433204773/181973740451351294722914594604383574000000000000), (843649826473846868193349728100901177467161/1512234562043575503351793130115826000000000000, 749481106328348694112490425042552069413003/1521362738474422035565184235529000000000000), (-89534391380883927547388057017227731425433204773/181973740451351294722914594604383574000000000000, 89737404489421741500583954326701515132065886363/181973740451351294722914594604383574000000000000), (-749481106328348694112490425042552069413003/1521362738474422035565184235529000000000000, 843649826473846868193349728100901177467161/1512234562043575503351793130115826000000000000)]

theorem terminal254Triangle0_vertex_pairs :
    ∀ v ∈ terminal254Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal254CoreField := by
  intro v hv
  simp only [terminal254Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal254CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal254CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal254CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal254CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal254CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal254CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal254CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal254CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal254CoreField]

theorem terminal254Triangle1_vertex_pairs :
    ∀ v ∈ terminal254Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal254CoreField := by
  intro v hv
  simp only [terminal254Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal254CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal254CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal254CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal254CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal254CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal254CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal254CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal254CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal254CoreField]

def terminal255CoreField : List QPoint := [(-55609329318965559681111268389490011950402149/112795553706959572964598419807195600000000000, -388580280365811613029210921043828538184446077/789568875948717010752188938650369200000000000), (-131251192106601162471418126807779167638611/302522990074211463045556490313522800000000000, -21419137748525135787930923641528304136567/43478440654528810440580122206600000000000), (388580280365811613029210921043828538184446077/789568875948717010752188938650369200000000000, -55609329318965559681111268389490011950402149/112795553706959572964598419807195600000000000), (21419137748525135787930923641528304136567/43478440654528810440580122206600000000000, -131251192106601162471418126807779167638611/302522990074211463045556490313522800000000000), (55609329318965559681111268389490011950402149/112795553706959572964598419807195600000000000, 388580280365811613029210921043828538184446077/789568875948717010752188938650369200000000000), (131251192106601162471418126807779167638611/302522990074211463045556490313522800000000000, 21419137748525135787930923641528304136567/43478440654528810440580122206600000000000), (-388580280365811613029210921043828538184446077/789568875948717010752188938650369200000000000, 55609329318965559681111268389490011950402149/112795553706959572964598419807195600000000000), (-21419137748525135787930923641528304136567/43478440654528810440580122206600000000000, 131251192106601162471418126807779167638611/302522990074211463045556490313522800000000000)]

theorem terminal255Triangle0_vertex_pairs :
    ∀ v ∈ terminal255Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal255CoreField := by
  intro v hv
  simp only [terminal255Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal255CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal255CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal255CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal255CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal255CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal255CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal255CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal255CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal255CoreField]

theorem terminal255Triangle1_vertex_pairs :
    ∀ v ∈ terminal255Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal255CoreField := by
  intro v hv
  simp only [terminal255Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal255CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal255CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal255CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal255CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal255CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal255CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal255CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal255CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal255CoreField]

def terminal256CoreField : List QPoint := [(-305260823394342843557837628214751551533500526647/619333436641449147483473190479812199600000000000, -304877064699810253051171948213340739892017113737/619333436641449147483473190479812199600000000000), (-312543277249771327936372376249437236718159/1008663622977328783932201656890654000000000000, -249952845356136937014224743288143073382229/507376067896040635780785541695500000000000), (304877064699810253051171948213340739892017113737/619333436641449147483473190479812199600000000000, -305260823394342843557837628214751551533500526647/619333436641449147483473190479812199600000000000), (249952845356136937014224743288143073382229/507376067896040635780785541695500000000000, -312543277249771327936372376249437236718159/1008663622977328783932201656890654000000000000), (305260823394342843557837628214751551533500526647/619333436641449147483473190479812199600000000000, 304877064699810253051171948213340739892017113737/619333436641449147483473190479812199600000000000), (312543277249771327936372376249437236718159/1008663622977328783932201656890654000000000000, 249952845356136937014224743288143073382229/507376067896040635780785541695500000000000), (-304877064699810253051171948213340739892017113737/619333436641449147483473190479812199600000000000, 305260823394342843557837628214751551533500526647/619333436641449147483473190479812199600000000000), (-249952845356136937014224743288143073382229/507376067896040635780785541695500000000000, 312543277249771327936372376249437236718159/1008663622977328783932201656890654000000000000)]

theorem terminal256Triangle0_vertex_pairs :
    ∀ v ∈ terminal256Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal256CoreField := by
  intro v hv
  simp only [terminal256Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal256CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal256CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal256CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal256CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal256CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal256CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal256CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal256CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal256CoreField]

theorem terminal256Triangle1_vertex_pairs :
    ∀ v ∈ terminal256Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal256CoreField := by
  intro v hv
  simp only [terminal256Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal256CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal256CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal256CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal256CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal256CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal256CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal256CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal256CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal256CoreField]

def terminal257CoreField : List QPoint := [(-381672059406320658482121476338068026295682964003/774556289108382176418839059845800342000000000000, -381384131772207154712358475471967582515826069021/774556289108382176418839059845800342000000000000), (-562653384997600813671507038213362456239423/3026752028656766170726706462841854000000000000, -750047250938441869507766132275367795513529/1522511080813262661331341279095500000000000), (381384131772207154712358475471967582515826069021/774556289108382176418839059845800342000000000000, -381672059406320658482121476338068026295682964003/774556289108382176418839059845800342000000000000), (750047250938441869507766132275367795513529/1522511080813262661331341279095500000000000, -562653384997600813671507038213362456239423/3026752028656766170726706462841854000000000000), (381672059406320658482121476338068026295682964003/774556289108382176418839059845800342000000000000, 381384131772207154712358475471967582515826069021/774556289108382176418839059845800342000000000000), (562653384997600813671507038213362456239423/3026752028656766170726706462841854000000000000, 750047250938441869507766132275367795513529/1522511080813262661331341279095500000000000), (-381384131772207154712358475471967582515826069021/774556289108382176418839059845800342000000000000, 381672059406320658482121476338068026295682964003/774556289108382176418839059845800342000000000000), (-750047250938441869507766132275367795513529/1522511080813262661331341279095500000000000, 562653384997600813671507038213362456239423/3026752028656766170726706462841854000000000000)]

theorem terminal257Triangle0_vertex_pairs :
    ∀ v ∈ terminal257Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal257CoreField := by
  intro v hv
  simp only [terminal257Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal257CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal257CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal257CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal257CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal257CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal257CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal257CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal257CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal257CoreField]

theorem terminal257Triangle1_vertex_pairs :
    ∀ v ∈ terminal257Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal257CoreField := by
  intro v hv
  simp only [terminal257Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal257CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal257CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal257CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal257CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal257CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal257CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal257CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal257CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal257CoreField]

def terminal258CoreField : List QPoint := [(-1527072358400298782067660407063042293375947532883/3099783913693625556506932130933912134000000000000, -1526688310021942879855007396605616703773437596269/3099783913693625556506932130933912134000000000000), (-94357435015529232545951205469287683421/1522894054283930627387258239258000000000000, -94357435015529232545951205469287683421/191534908097589061424633158000000000000), (1526688310021942879855007396605616703773437596269/3099783913693625556506932130933912134000000000000, -1527072358400298782067660407063042293375947532883/3099783913693625556506932130933912134000000000000), (94357435015529232545951205469287683421/191534908097589061424633158000000000000, -94357435015529232545951205469287683421/1522894054283930627387258239258000000000000), (1527072358400298782067660407063042293375947532883/3099783913693625556506932130933912134000000000000, 1526688310021942879855007396605616703773437596269/3099783913693625556506932130933912134000000000000), (94357435015529232545951205469287683421/1522894054283930627387258239258000000000000, 94357435015529232545951205469287683421/191534908097589061424633158000000000000), (-1526688310021942879855007396605616703773437596269/3099783913693625556506932130933912134000000000000, 1527072358400298782067660407063042293375947532883/3099783913693625556506932130933912134000000000000), (-94357435015529232545951205469287683421/191534908097589061424633158000000000000, 94357435015529232545951205469287683421/1522894054283930627387258239258000000000000)]

theorem terminal258Triangle0_vertex_pairs :
    ∀ v ∈ terminal258Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal258CoreField := by
  intro v hv
  simp only [terminal258Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal258CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal258CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal258CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal258CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal258CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal258CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal258CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal258CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal258CoreField]

theorem terminal258Triangle1_vertex_pairs :
    ∀ v ∈ terminal258Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal258CoreField := by
  intro v hv
  simp only [terminal258Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal258CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal258CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal258CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal258CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal258CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal258CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal258CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal258CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal258CoreField]

end
end ElevenSquare.Tasks.T07
