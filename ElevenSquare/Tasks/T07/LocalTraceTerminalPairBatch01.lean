import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairData
import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch01
import Mathlib.Tactic.NormNum

/-! Exact source-owned minus core vertex witnesses. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def terminal10CoreField : List QPoint := [(-1519209367926349194557538701983698829718589880627/3076082395297669089549595411350652006000000000000, 1511190402882301269352769402595967088238748434739/3076082395297669089549595411350652006000000000000), (-3853346439499642502825002714498642508495479/7821884059162699423494095238382000000000000, -2569713979596390909306491652902923563/1971240942329309330517665130640625000000), (-1511190402882301269352769402595967088238748434739/3076082395297669089549595411350652006000000000000, -1519209367926349194557538701983698829718589880627/3076082395297669089549595411350652006000000000000), (2569713979596390909306491652902923563/1971240942329309330517665130640625000000, -3853346439499642502825002714498642508495479/7821884059162699423494095238382000000000000), (1519209367926349194557538701983698829718589880627/3076082395297669089549595411350652006000000000000, -1511190402882301269352769402595967088238748434739/3076082395297669089549595411350652006000000000000), (3853346439499642502825002714498642508495479/7821884059162699423494095238382000000000000, 2569713979596390909306491652902923563/1971240942329309330517665130640625000000), (1511190402882301269352769402595967088238748434739/3076082395297669089549595411350652006000000000000, 1519209367926349194557538701983698829718589880627/3076082395297669089549595411350652006000000000000), (-2569713979596390909306491652902923563/1971240942329309330517665130640625000000, 3853346439499642502825002714498642508495479/7821884059162699423494095238382000000000000)]

theorem terminal10Triangle0_vertex_pairs :
    ∀ v ∈ terminal10Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal10CoreField := by
  intro v hv
  simp only [terminal10Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal10CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal10CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal10CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal10CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal10CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal10CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal10CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal10CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal10CoreField]

theorem terminal10Triangle1_vertex_pairs :
    ∀ v ∈ terminal10Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal10CoreField := by
  intro v hv
  simp only [terminal10Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal10CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal10CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal10CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal10CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal10CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal10CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal10CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal10CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal10CoreField]

def terminal11CoreField : List QPoint := [(-6078364803234315302075179074826381890184317361691/12304337981496259406363256857627162678000000000000, 6043234087517902701761412058623449717748242970139/12304337981496259406363256857627162678000000000000), (-5780017640188479785644646759504522196160419/11732830187209112148358009691974000000000000, -8443345932959570130578472573823891707/5913724892746528300583674239906250000000), (-6043234087517902701761412058623449717748242970139/12304337981496259406363256857627162678000000000000, -6078364803234315302075179074826381890184317361691/12304337981496259406363256857627162678000000000000), (8443345932959570130578472573823891707/5913724892746528300583674239906250000000, -5780017640188479785644646759504522196160419/11732830187209112148358009691974000000000000), (6078364803234315302075179074826381890184317361691/12304337981496259406363256857627162678000000000000, -6043234087517902701761412058623449717748242970139/12304337981496259406363256857627162678000000000000), (5780017640188479785644646759504522196160419/11732830187209112148358009691974000000000000, 8443345932959570130578472573823891707/5913724892746528300583674239906250000000), (6043234087517902701761412058623449717748242970139/12304337981496259406363256857627162678000000000000, 6078364803234315302075179074826381890184317361691/12304337981496259406363256857627162678000000000000), (-8443345932959570130578472573823891707/5913724892746528300583674239906250000000, 5780017640188479785644646759504522196160419/11732830187209112148358009691974000000000000)]

theorem terminal11Triangle0_vertex_pairs :
    ∀ v ∈ terminal11Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal11CoreField := by
  intro v hv
  simp only [terminal11Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal11CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal11CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal11CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal11CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal11CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal11CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal11CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal11CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal11CoreField]

theorem terminal11Triangle1_vertex_pairs :
    ∀ v ∈ terminal11Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal11CoreField := by
  intro v hv
  simp only [terminal11Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal11CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal11CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal11CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal11CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal11CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal11CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal11CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal11CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal11CoreField]

def terminal12CoreField : List QPoint := [(-75998651704822779673981956328304416811404764463/153804339540361220431455531914727978800000000000, 75521332023492064126417475730014063785931894063/153804339540361220431455531914727978800000000000), (-1156003087515299454890487756502335370159473/2346566931652381632533463793173200000000000, -367101997085198701329498807557560509/236549085852054600053776592053750000000), (-75521332023492064126417475730014063785931894063/153804339540361220431455531914727978800000000000, -75998651704822779673981956328304416811404764463/153804339540361220431455531914727978800000000000), (367101997085198701329498807557560509/236549085852054600053776592053750000000, -1156003087515299454890487756502335370159473/2346566931652381632533463793173200000000000), (75998651704822779673981956328304416811404764463/153804339540361220431455531914727978800000000000, -75521332023492064126417475730014063785931894063/153804339540361220431455531914727978800000000000), (1156003087515299454890487756502335370159473/2346566931652381632533463793173200000000000, 367101997085198701329498807557560509/236549085852054600053776592053750000000), (75521332023492064126417475730014063785931894063/153804339540361220431455531914727978800000000000, 75998651704822779673981956328304416811404764463/153804339540361220431455531914727978800000000000), (-367101997085198701329498807557560509/236549085852054600053776592053750000000, 1156003087515299454890487756502335370159473/2346566931652381632533463793173200000000000)]

theorem terminal12Triangle0_vertex_pairs :
    ∀ v ∈ terminal12Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal12CoreField := by
  intro v hv
  simp only [terminal12Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal12CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal12CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal12CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal12CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal12CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal12CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal12CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal12CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal12CoreField]

theorem terminal12Triangle1_vertex_pairs :
    ∀ v ∈ terminal12Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal12CoreField := by
  intro v hv
  simp only [terminal12Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal12CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal12CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal12CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal12CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal12CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal12CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal12CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal12CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal12CoreField]

def terminal13CoreField : List QPoint := [(-1216283894261000318752027970122792123315219334951/2460871425277893142543169575786847207600000000000, 1208035806893529394093436747204340296792650407719/2460871425277893142543169575786847207600000000000), (-3853342034275677480440586760512951817769371/7821893001268291452112713786166000000000000, -3303917973766788311965489268018044581/1971243195884146031278405692078125000000), (-1208035806893529394093436747204340296792650407719/2460871425277893142543169575786847207600000000000, -1216283894261000318752027970122792123315219334951/2460871425277893142543169575786847207600000000000), (3303917973766788311965489268018044581/1971243195884146031278405692078125000000, -3853342034275677480440586760512951817769371/7821893001268291452112713786166000000000000), (1216283894261000318752027970122792123315219334951/2460871425277893142543169575786847207600000000000, -1208035806893529394093436747204340296792650407719/2460871425277893142543169575786847207600000000000), (3853342034275677480440586760512951817769371/7821893001268291452112713786166000000000000, 3303917973766788311965489268018044581/1971243195884146031278405692078125000000), (1208035806893529394093436747204340296792650407719/2460871425277893142543169575786847207600000000000, 1216283894261000318752027970122792123315219334951/2460871425277893142543169575786847207600000000000), (-3303917973766788311965489268018044581/1971243195884146031278405692078125000000, 3853342034275677480440586760512951817769371/7821893001268291452112713786166000000000000)]

theorem terminal13Triangle0_vertex_pairs :
    ∀ v ∈ terminal13Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal13CoreField := by
  intro v hv
  simp only [terminal13Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal13CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal13CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal13CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal13CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal13CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal13CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal13CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal13CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal13CoreField]

theorem terminal13Triangle1_vertex_pairs :
    ∀ v ∈ terminal13Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal13CoreField := by
  intro v hv
  simp only [terminal13Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal13CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal13CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal13CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal13CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal13CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal13CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal13CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal13CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal13CoreField]

def terminal14CoreField : List QPoint := [(-217248100290603567485706496195016325104000920829/439441709677818312536582514993062906000000000000, 1509662876284191539705729313752497075215673311979/3076091967744728187756077604951440342000000000000), (-11560020963399073248539941668555549647460987/23465689436261398389726529664246000000000000, -10645957915470762338555465419169254761/5913732216799747578056081064578125000000), (-1509662876284191539705729313752497075215673311979/3076091967744728187756077604951440342000000000000, -217248100290603567485706496195016325104000920829/439441709677818312536582514993062906000000000000), (10645957915470762338555465419169254761/5913732216799747578056081064578125000000, -11560020963399073248539941668555549647460987/23465689436261398389726529664246000000000000), (217248100290603567485706496195016325104000920829/439441709677818312536582514993062906000000000000, -1509662876284191539705729313752497075215673311979/3076091967744728187756077604951440342000000000000), (11560020963399073248539941668555549647460987/23465689436261398389726529664246000000000000, 10645957915470762338555465419169254761/5913732216799747578056081064578125000000), (1509662876284191539705729313752497075215673311979/3076091967744728187756077604951440342000000000000, 217248100290603567485706496195016325104000920829/439441709677818312536582514993062906000000000000), (-10645957915470762338555465419169254761/5913732216799747578056081064578125000000, 11560020963399073248539941668555549647460987/23465689436261398389726529664246000000000000)]

theorem terminal14Triangle0_vertex_pairs :
    ∀ v ∈ terminal14Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal14CoreField := by
  intro v hv
  simp only [terminal14Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal14CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal14CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal14CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal14CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal14CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal14CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal14CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal14CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal14CoreField]

theorem terminal14Triangle1_vertex_pairs :
    ∀ v ∈ terminal14Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal14CoreField := by
  intro v hv
  simp only [terminal14Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal14CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal14CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal14CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal14CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal14CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal14CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal14CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal14CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal14CoreField]

def terminal15CoreField : List QPoint := [(-6331398696177447989008673733204056884366021283/12803724658687057543714460144365894000000000000, 6282126923767641997066333835703223160915962531/12803724658687057543714460144365894000000000000), (-1445001932108639621319927715759179535506669/2933212576736673553187475356122000000000000, -367101997085198701329498807557560509/190765646249783659806677637625000000000), (-6282126923767641997066333835703223160915962531/12803724658687057543714460144365894000000000000, -6331398696177447989008673733204056884366021283/12803724658687057543714460144365894000000000000), (367101997085198701329498807557560509/190765646249783659806677637625000000000, -1445001932108639621319927715759179535506669/2933212576736673553187475356122000000000000), (6331398696177447989008673733204056884366021283/12803724658687057543714460144365894000000000000, -6282126923767641997066333835703223160915962531/12803724658687057543714460144365894000000000000), (1445001932108639621319927715759179535506669/2933212576736673553187475356122000000000000, 367101997085198701329498807557560509/190765646249783659806677637625000000000), (6282126923767641997066333835703223160915962531/12803724658687057543714460144365894000000000000, 6331398696177447989008673733204056884366021283/12803724658687057543714460144365894000000000000), (-367101997085198701329498807557560509/190765646249783659806677637625000000000, 1445001932108639621319927715759179535506669/2933212576736673553187475356122000000000000)]

theorem terminal15Triangle0_vertex_pairs :
    ∀ v ∈ terminal15Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal15CoreField := by
  intro v hv
  simp only [terminal15Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal15CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal15CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal15CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal15CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal15CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal15CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal15CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal15CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal15CoreField]

theorem terminal15Triangle1_vertex_pairs :
    ∀ v ∈ terminal15Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal15CoreField := by
  intro v hv
  simp only [terminal15Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal15CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal15CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal15CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal15CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal15CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal15CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal15CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal15CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal15CoreField]

def terminal16CoreField : List QPoint := [(-23850783102558498806341304494229036855033082827/48221656534846471570383197816905942000000000000, 23498759211561608090647870308389096249621720011/48221656534846471570383197816905942000000000000), (-1444983301773454512123477989792567923812417/2933233441649721619964251967618000000000000, -21658892647484731190940429645896070031/5913777100100245201540830579875000000000), (-23498759211561608090647870308389096249621720011/48221656534846471570383197816905942000000000000, -23850783102558498806341304494229036855033082827/48221656534846471570383197816905942000000000000), (21658892647484731190940429645896070031/5913777100100245201540830579875000000000, -1444983301773454512123477989792567923812417/2933233441649721619964251967618000000000000), (23850783102558498806341304494229036855033082827/48221656534846471570383197816905942000000000000, -23498759211561608090647870308389096249621720011/48221656534846471570383197816905942000000000000), (1444983301773454512123477989792567923812417/2933233441649721619964251967618000000000000, 21658892647484731190940429645896070031/5913777100100245201540830579875000000000), (23498759211561608090647870308389096249621720011/48221656534846471570383197816905942000000000000, 23850783102558498806341304494229036855033082827/48221656534846471570383197816905942000000000000), (-21658892647484731190940429645896070031/5913777100100245201540830579875000000000, 1444983301773454512123477989792567923812417/2933233441649721619964251967618000000000000)]

theorem terminal16Triangle0_vertex_pairs :
    ∀ v ∈ terminal16Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal16CoreField := by
  intro v hv
  simp only [terminal16Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal16CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal16CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal16CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal16CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal16CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal16CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal16CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal16CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal16CoreField]

theorem terminal16Triangle1_vertex_pairs :
    ∀ v ∈ terminal16Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal16CoreField := by
  intro v hv
  simp only [terminal16Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal16CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal16CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal16CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal16CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal16CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal16CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal16CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal16CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal16CoreField]

def terminal17CoreField : List QPoint := [(-1229394597584915060130899473002595310953739556367/2469102032084653455799223251067559556400000000000, 1194873903712731984679519414876984537941825986063/2469102032084653455799223251067559556400000000000), (-11559440211232318643209642870224969062748387/23466732681913801728565360239046000000000000, -41482285918063976687733365254004337517/5913995131530696000142479898953125000000), (-1194873903712731984679519414876984537941825986063/2469102032084653455799223251067559556400000000000, -1229394597584915060130899473002595310953739556367/2469102032084653455799223251067559556400000000000), (41482285918063976687733365254004337517/5913995131530696000142479898953125000000, -11559440211232318643209642870224969062748387/23466732681913801728565360239046000000000000), (1229394597584915060130899473002595310953739556367/2469102032084653455799223251067559556400000000000, -1194873903712731984679519414876984537941825986063/2469102032084653455799223251067559556400000000000), (11559440211232318643209642870224969062748387/23466732681913801728565360239046000000000000, 41482285918063976687733365254004337517/5913995131530696000142479898953125000000), (1194873903712731984679519414876984537941825986063/2469102032084653455799223251067559556400000000000, 1229394597584915060130899473002595310953739556367/2469102032084653455799223251067559556400000000000), (-41482285918063976687733365254004337517/5913995131530696000142479898953125000000, 11559440211232318643209642870224969062748387/23466732681913801728565360239046000000000000)]

theorem terminal17Triangle0_vertex_pairs :
    ∀ v ∈ terminal17Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal17CoreField := by
  intro v hv
  simp only [terminal17Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal17CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal17CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal17CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal17CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal17CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal17CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal17CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal17CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal17CoreField]

theorem terminal17Triangle1_vertex_pairs :
    ∀ v ∈ terminal17Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal17CoreField := by
  intro v hv
  simp only [terminal17Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal17CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal17CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal17CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal17CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal17CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal17CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal17CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal17CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal17CoreField]

def terminal18CoreField : List QPoint := [(-1547037626473072518451635423808064200599951955883/3086711726987845738647788537842711894000000000000, 1483262901414810718184614966882005523291444539307/3086711726987845738647788537842711894000000000000), (-11558746392467848369617255117478685273386377/23468141063544546235997781515026000000000000, -61305679188643222184526300862112605003/5914350066417476369959118325359375000000), (-1483262901414810718184614966882005523291444539307/3086711726987845738647788537842711894000000000000, -1547037626473072518451635423808064200599951955883/3086711726987845738647788537842711894000000000000), (61305679188643222184526300862112605003/5914350066417476369959118325359375000000, -11558746392467848369617255117478685273386377/23468141063544546235997781515026000000000000), (1547037626473072518451635423808064200599951955883/3086711726987845738647788537842711894000000000000, -1483262901414810718184614966882005523291444539307/3086711726987845738647788537842711894000000000000), (11558746392467848369617255117478685273386377/23468141063544546235997781515026000000000000, 61305679188643222184526300862112605003/5914350066417476369959118325359375000000), (1483262901414810718184614966882005523291444539307/3086711726987845738647788537842711894000000000000, 1547037626473072518451635423808064200599951955883/3086711726987845738647788537842711894000000000000), (-61305679188643222184526300862112605003/5914350066417476369959118325359375000000, 11558746392467848369617255117478685273386377/23468141063544546235997781515026000000000000)]

theorem terminal18Triangle0_vertex_pairs :
    ∀ v ∈ terminal18Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal18CoreField := by
  intro v hv
  simp only [terminal18Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal18CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal18CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal18CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal18CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal18CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal18CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal18CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal18CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal18CoreField]

theorem terminal18Triangle1_vertex_pairs :
    ∀ v ∈ terminal18Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal18CoreField := by
  intro v hv
  simp only [terminal18Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal18CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal18CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal18CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal18CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal18CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal18CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal18CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal18CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal18CoreField]

def terminal19CoreField : List QPoint := [(-1245867169333029509403776396360502916534596129823/2469750881635821854892181682505408369200000000000, 1178345141925979704436348440656104828293044730911/2469750881635821854892181682505408369200000000000), (-186415886417648794777591300969382129393763/378549881904677523903407734982000000000000, -6240697881478651360101479728478528653/454987838827737408537749681468750000000), (-1178345141925979704436348440656104828293044730911/2469750881635821854892181682505408369200000000000, -1245867169333029509403776396360502916534596129823/2469750881635821854892181682505408369200000000000), (6240697881478651360101479728478528653/454987838827737408537749681468750000000, -186415886417648794777591300969382129393763/378549881904677523903407734982000000000000), (1245867169333029509403776396360502916534596129823/2469750881635821854892181682505408369200000000000, -1178345141925979704436348440656104828293044730911/2469750881635821854892181682505408369200000000000), (186415886417648794777591300969382129393763/378549881904677523903407734982000000000000, 6240697881478651360101479728478528653/454987838827737408537749681468750000000), (1178345141925979704436348440656104828293044730911/2469750881635821854892181682505408369200000000000, 1245867169333029509403776396360502916534596129823/2469750881635821854892181682505408369200000000000), (-6240697881478651360101479728478528653/454987838827737408537749681468750000000, 186415886417648794777591300969382129393763/378549881904677523903407734982000000000000)]

theorem terminal19Triangle0_vertex_pairs :
    ∀ v ∈ terminal19Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal19CoreField := by
  intro v hv
  simp only [terminal19Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal19CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal19CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal19CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal19CoreField[5]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal19CoreField 5 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal19CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal19CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal19CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal19CoreField]

theorem terminal19Triangle1_vertex_pairs :
    ∀ v ∈ terminal19Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal19CoreField := by
  intro v hv
  simp only [terminal19Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal19CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal19CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal19CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal19CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal19CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal19CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal19CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal19CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal19CoreField]

end
end ElevenSquare.Tasks.T07
