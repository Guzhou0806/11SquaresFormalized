import ElevenSquare.Tasks.T07.LocalMinkowskiRow1
import ElevenSquare.Tasks.T07.LocalTraceTerminalPairData
import ElevenSquare.Tasks.T07.LocalTraceTerminalBatch06
import Mathlib.Tactic.NormNum

/-! Exact source-owned minus core vertex witnesses. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def terminal240CoreField : List QPoint := [(-1581302667664130272400709633065935215899488617056121827/3178735705210314749935634627420110496850886000000000000, -1545844065608863977471909193724128503223572240192963613/3178735705210314749935634627420110496850886000000000000), (-17126032165313336835753346540966299440694529609/3065799559887277960870779988960779410000000000000, -4747951954551538239955304645509086942061299/9638454350752257170745661434107078125000000), (1545844065608863977471909193724128503223572240192963613/3178735705210314749935634627420110496850886000000000000, -1581302667664130272400709633065935215899488617056121827/3178735705210314749935634627420110496850886000000000000), (4747951954551538239955304645509086942061299/9638454350752257170745661434107078125000000, -17126032165313336835753346540966299440694529609/3065799559887277960870779988960779410000000000000), (1581302667664130272400709633065935215899488617056121827/3178735705210314749935634627420110496850886000000000000, 1545844065608863977471909193724128503223572240192963613/3178735705210314749935634627420110496850886000000000000), (17126032165313336835753346540966299440694529609/3065799559887277960870779988960779410000000000000, 4747951954551538239955304645509086942061299/9638454350752257170745661434107078125000000), (-1545844065608863977471909193724128503223572240192963613/3178735705210314749935634627420110496850886000000000000, 1581302667664130272400709633065935215899488617056121827/3178735705210314749935634627420110496850886000000000000), (-4747951954551538239955304645509086942061299/9638454350752257170745661434107078125000000, 17126032165313336835753346540966299440694529609/3065799559887277960870779988960779410000000000000)]

theorem terminal240Triangle0_vertex_pairs :
    ∀ v ∈ terminal240Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal240CoreField := by
  intro v hv
  simp only [terminal240Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal240CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal240CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal240CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[3]'(by decide), terminal240CoreField[0]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 3 (by decide),
         List.getElem_mem terminal240CoreField 0 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal240CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal240CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal240CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal240CoreField]

def terminal241CoreField : List QPoint := [(-396485083320860822218787063388402646774728388661681243/799303176535108124313829758451146793058998000000000000, -389871956250920357249041332460353778621123521054190501/799303176535108124313829758451146793058998000000000000), (-12739622612698279151548728979908964896511837891/3074703511729507682506110900595395974000000000000, -23809395269139953073444263342181769020671193/48332235785486476397543242275455796875000000), (389871956250920357249041332460353778621123521054190501/799303176535108124313829758451146793058998000000000000, -396485083320860822218787063388402646774728388661681243/799303176535108124313829758451146793058998000000000000), (23809395269139953073444263342181769020671193/48332235785486476397543242275455796875000000, -12739622612698279151548728979908964896511837891/3074703511729507682506110900595395974000000000000), (396485083320860822218787063388402646774728388661681243/799303176535108124313829758451146793058998000000000000, 389871956250920357249041332460353778621123521054190501/799303176535108124313829758451146793058998000000000000), (12739622612698279151548728979908964896511837891/3074703511729507682506110900595395974000000000000, 23809395269139953073444263342181769020671193/48332235785486476397543242275455796875000000), (-389871956250920357249041332460353778621123521054190501/799303176535108124313829758451146793058998000000000000, 396485083320860822218787063388402646774728388661681243/799303176535108124313829758451146793058998000000000000), (-23809395269139953073444263342181769020671193/48332235785486476397543242275455796875000000, 12739622612698279151548728979908964896511837891/3074703511729507682506110900595395974000000000000)]

theorem terminal241Triangle0_vertex_pairs :
    ∀ v ∈ terminal241Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal241CoreField := by
  intro v hv
  simp only [terminal241Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal241CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal241CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal241CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[3]'(by decide), terminal241CoreField[0]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 3 (by decide),
         List.getElem_mem terminal241CoreField 0 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal241CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal241CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal241CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal241CoreField]

def terminal242CoreField : List QPoint := [(-185490186997345766510555392052737642245120440892989/375020133678077030198058913016999693065360000000000, -1284254127448629374029980313538913147067082425033813/2625140935746539211386412391118997851457520000000000), (-65159103992192923059784479435165833375522339/24090887055909053749731519153948742000000000000, -3411290109360316421016000493831157618719413/6924658538634393144504604528298000000000000), (1284254127448629374029980313538913147067082425033813/2625140935746539211386412391118997851457520000000000, -185490186997345766510555392052737642245120440892989/375020133678077030198058913016999693065360000000000), (3411290109360316421016000493831157618719413/6924658538634393144504604528298000000000000, -65159103992192923059784479435165833375522339/24090887055909053749731519153948742000000000000), (185490186997345766510555392052737642245120440892989/375020133678077030198058913016999693065360000000000, 1284254127448629374029980313538913147067082425033813/2625140935746539211386412391118997851457520000000000), (65159103992192923059784479435165833375522339/24090887055909053749731519153948742000000000000, 3411290109360316421016000493831157618719413/6924658538634393144504604528298000000000000), (-1284254127448629374029980313538913147067082425033813/2625140935746539211386412391118997851457520000000000, 185490186997345766510555392052737642245120440892989/375020133678077030198058913016999693065360000000000), (-3411290109360316421016000493831157618719413/6924658538634393144504604528298000000000000, 65159103992192923059784479435165833375522339/24090887055909053749731519153948742000000000000)]

theorem terminal242Triangle0_vertex_pairs :
    ∀ v ∈ terminal242Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal242CoreField := by
  intro v hv
  simp only [terminal242Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal242CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal242CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal242CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal242CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal242CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal242CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal242CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal242CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal242CoreField]

theorem terminal242Triangle1_vertex_pairs :
    ∀ v ∈ terminal242Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal242CoreField := by
  intro v hv
  simp only [terminal242Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal242CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal242CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal242CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal242CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal242CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal242CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal242CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal242CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal242CoreField]

def terminal243CoreField : List QPoint := [(-11885239004771555155730642500314488093874545731/24035037061347850860108697549548218000000000000, -11792752325385405024470680224893450997249569533/24035037061347850860108697549548218000000000000), (-1450934278233793008859091686501236707964717/754028305546621396577468803520186000000000000, -747405242758007050996479498522227740377741/1517159568504268403576395982938000000000000), (11792752325385405024470680224893450997249569533/24035037061347850860108697549548218000000000000, -11885239004771555155730642500314488093874545731/24035037061347850860108697549548218000000000000), (747405242758007050996479498522227740377741/1517159568504268403576395982938000000000000, -1450934278233793008859091686501236707964717/754028305546621396577468803520186000000000000), (11885239004771555155730642500314488093874545731/24035037061347850860108697549548218000000000000, 11792752325385405024470680224893450997249569533/24035037061347850860108697549548218000000000000), (1450934278233793008859091686501236707964717/754028305546621396577468803520186000000000000, 747405242758007050996479498522227740377741/1517159568504268403576395982938000000000000), (-11792752325385405024470680224893450997249569533/24035037061347850860108697549548218000000000000, 11885239004771555155730642500314488093874545731/24035037061347850860108697549548218000000000000), (-747405242758007050996479498522227740377741/1517159568504268403576395982938000000000000, 1450934278233793008859091686501236707964717/754028305546621396577468803520186000000000000)]

theorem terminal243Triangle0_vertex_pairs :
    ∀ v ∈ terminal243Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal243CoreField := by
  intro v hv
  simp only [terminal243Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal243CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal243CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal243CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal243CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal243CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal243CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal243CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal243CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal243CoreField]

theorem terminal243Triangle1_vertex_pairs :
    ∀ v ∈ terminal243Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal243CoreField := by
  intro v hv
  simp only [terminal243Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal243CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal243CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal243CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal243CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal243CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal243CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal243CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal243CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal243CoreField]

def terminal244CoreField : List QPoint := [(-1521694705072105984081134645028838303916951516331/3078032551530474475279976643194495158000000000000, -1510615989657646728349650869211002421131644386581/3078032551530474475279976643194495158000000000000), (-6013274986532293184188099691186155390729/3340943401946245998429876174994000000000000, -5795301997116574491950165898706715625927/11763885218120584501513648503500000000000), (1510615989657646728349650869211002421131644386581/3078032551530474475279976643194495158000000000000, -1521694705072105984081134645028838303916951516331/3078032551530474475279976643194495158000000000000), (5795301997116574491950165898706715625927/11763885218120584501513648503500000000000, -6013274986532293184188099691186155390729/3340943401946245998429876174994000000000000), (1521694705072105984081134645028838303916951516331/3078032551530474475279976643194495158000000000000, 1510615989657646728349650869211002421131644386581/3078032551530474475279976643194495158000000000000), (6013274986532293184188099691186155390729/3340943401946245998429876174994000000000000, 5795301997116574491950165898706715625927/11763885218120584501513648503500000000000), (-1510615989657646728349650869211002421131644386581/3078032551530474475279976643194495158000000000000, 1521694705072105984081134645028838303916951516331/3078032551530474475279976643194495158000000000000), (-5795301997116574491950165898706715625927/11763885218120584501513648503500000000000, 6013274986532293184188099691186155390729/3340943401946245998429876174994000000000000)]

theorem terminal244Triangle0_vertex_pairs :
    ∀ v ∈ terminal244Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal244CoreField := by
  intro v hv
  simp only [terminal244Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal244CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal244CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal244CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal244CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal244CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal244CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal244CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal244CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal244CoreField]

theorem terminal244Triangle1_vertex_pairs :
    ∀ v ∈ terminal244Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal244CoreField := by
  intro v hv
  simp only [terminal244Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal244CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal244CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal244CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal244CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal244CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal244CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal244CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal244CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal244CoreField]

def terminal245CoreField : List QPoint := [(-1553141651631345649211903944440058146666612199/3142429734084251672272546505090570800000000000, -1542612508336712335695852809100014692846138201/3142429734084251672272546505090570800000000000), (-144461233008775255027851295573479443317551/86218021521809793841244073788330800000000000, -29911306899922766717066532133764195644457/60716916564654784395242305484740000000000), (1542612508336712335695852809100014692846138201/3142429734084251672272546505090570800000000000, -1553141651631345649211903944440058146666612199/3142429734084251672272546505090570800000000000), (29911306899922766717066532133764195644457/60716916564654784395242305484740000000000, -144461233008775255027851295573479443317551/86218021521809793841244073788330800000000000), (1553141651631345649211903944440058146666612199/3142429734084251672272546505090570800000000000, 1542612508336712335695852809100014692846138201/3142429734084251672272546505090570800000000000), (144461233008775255027851295573479443317551/86218021521809793841244073788330800000000000, 29911306899922766717066532133764195644457/60716916564654784395242305484740000000000), (-1542612508336712335695852809100014692846138201/3142429734084251672272546505090570800000000000, 1553141651631345649211903944440058146666612199/3142429734084251672272546505090570800000000000), (-29911306899922766717066532133764195644457/60716916564654784395242305484740000000000, 144461233008775255027851295573479443317551/86218021521809793841244073788330800000000000)]

theorem terminal245Triangle0_vertex_pairs :
    ∀ v ∈ terminal245Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal245CoreField := by
  intro v hv
  simp only [terminal245Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal245CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal245CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal245CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal245CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal245CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal245CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal245CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal245CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal245CoreField]

theorem terminal245Triangle1_vertex_pairs :
    ∀ v ∈ terminal245Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal245CoreField := by
  intro v hv
  simp only [terminal245Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal245CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal245CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal245CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal245CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal245CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal245CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal245CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal245CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal245CoreField]

def terminal246CoreField : List QPoint := [(-304492586623643191274637872917474853549591767903/616226101552742818052101891162111223600000000000, -302581020680903031405776054039547234825920825953/616226101552742818052101891162111223600000000000), (-2341102320170295788697595358898496713358431/1509194903052066764946984201898366000000000000, -747971387368100226391755205755043466478267/1518304731440711031133786923439000000000000), (302581020680903031405776054039547234825920825953/616226101552742818052101891162111223600000000000, -304492586623643191274637872917474853549591767903/616226101552742818052101891162111223600000000000), (747971387368100226391755205755043466478267/1518304731440711031133786923439000000000000, -2341102320170295788697595358898496713358431/1509194903052066764946984201898366000000000000), (304492586623643191274637872917474853549591767903/616226101552742818052101891162111223600000000000, 302581020680903031405776054039547234825920825953/616226101552742818052101891162111223600000000000), (2341102320170295788697595358898496713358431/1509194903052066764946984201898366000000000000, 747971387368100226391755205755043466478267/1518304731440711031133786923439000000000000), (-302581020680903031405776054039547234825920825953/616226101552742818052101891162111223600000000000, 304492586623643191274637872917474853549591767903/616226101552742818052101891162111223600000000000), (-747971387368100226391755205755043466478267/1518304731440711031133786923439000000000000, 2341102320170295788697595358898496713358431/1509194903052066764946984201898366000000000000)]

theorem terminal246Triangle0_vertex_pairs :
    ∀ v ∈ terminal246Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal246CoreField := by
  intro v hv
  simp only [terminal246Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal246CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal246CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal246CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal246CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal246CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal246CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal246CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal246CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal246CoreField]

theorem terminal246Triangle1_vertex_pairs :
    ∀ v ∈ terminal246Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal246CoreField := by
  intro v hv
  simp only [terminal246Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal246CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal246CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal246CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal246CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal246CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal246CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal246CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal246CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal246CoreField]

def terminal247CoreField : List QPoint := [(-95177940534886225782361165146066023278939746367/192667541056806497444399131111105078000000000000, -94628157848717739780641433382531487202671277569/192667541056806497444399131111105078000000000000), (-718028627989838949930506689886122841606003/503191508413305395488909274939174000000000000, -249386700746043761618949036055327347281703/506228881703526554817816171971000000000000), (94628157848717739780641433382531487202671277569/192667541056806497444399131111105078000000000000, -95177940534886225782361165146066023278939746367/192667541056806497444399131111105078000000000000), (249386700746043761618949036055327347281703/506228881703526554817816171971000000000000, -718028627989838949930506689886122841606003/503191508413305395488909274939174000000000000), (95177940534886225782361165146066023278939746367/192667541056806497444399131111105078000000000000, 94628157848717739780641433382531487202671277569/192667541056806497444399131111105078000000000000), (718028627989838949930506689886122841606003/503191508413305395488909274939174000000000000, 249386700746043761618949036055327347281703/506228881703526554817816171971000000000000), (-94628157848717739780641433382531487202671277569/192667541056806497444399131111105078000000000000, 95177940534886225782361165146066023278939746367/192667541056806497444399131111105078000000000000), (-249386700746043761618949036055327347281703/506228881703526554817816171971000000000000, 718028627989838949930506689886122841606003/503191508413305395488909274939174000000000000)]

theorem terminal247Triangle0_vertex_pairs :
    ∀ v ∈ terminal247Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal247CoreField := by
  intro v hv
  simp only [terminal247Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal247CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal247CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal247CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal247CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal247CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal247CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal247CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal247CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal247CoreField]

theorem terminal247Triangle1_vertex_pairs :
    ∀ v ∈ terminal247Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal247CoreField := by
  intro v hv
  simp only [terminal247Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal247CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal247CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal247CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal247CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal247CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal247CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal247CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal247CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal247CoreField]

def terminal248CoreField : List QPoint := [(-31086350302982755115540964004493305685705615027/62943501778228526834935137776329286000000000000, -30922378059451973538078820827278588710194658061/62943501778228526834935137776329286000000000000), (-3934044538102460292538343609631011384871753/3019908486390439313562004320106514000000000000, -9718815806599510952232974163336631392363/19728164352285396231688862526500000000000), (30922378059451973538078820827278588710194658061/62943501778228526834935137776329286000000000000, -31086350302982755115540964004493305685705615027/62943501778228526834935137776329286000000000000), (9718815806599510952232974163336631392363/19728164352285396231688862526500000000000, -3934044538102460292538343609631011384871753/3019908486390439313562004320106514000000000000), (31086350302982755115540964004493305685705615027/62943501778228526834935137776329286000000000000, 30922378059451973538078820827278588710194658061/62943501778228526834935137776329286000000000000), (3934044538102460292538343609631011384871753/3019908486390439313562004320106514000000000000, 9718815806599510952232974163336631392363/19728164352285396231688862526500000000000), (-30922378059451973538078820827278588710194658061/62943501778228526834935137776329286000000000000, 31086350302982755115540964004493305685705615027/62943501778228526834935137776329286000000000000), (-9718815806599510952232974163336631392363/19728164352285396231688862526500000000000, 3934044538102460292538343609631011384871753/3019908486390439313562004320106514000000000000)]

theorem terminal248Triangle0_vertex_pairs :
    ∀ v ∈ terminal248Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal248CoreField := by
  intro v hv
  simp only [terminal248Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal248CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal248CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal248CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal248CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal248CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal248CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal248CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal248CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal248CoreField]

theorem terminal248Triangle1_vertex_pairs :
    ∀ v ∈ terminal248Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal248CoreField := by
  intro v hv
  simp only [terminal248Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal248CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal248CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal248CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal248CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal248CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal248CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal248CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal248CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal248CoreField]

def terminal249CoreField : List QPoint := [(-380903820477412686201112180219148057774414099819/771445824682932916801210275945030502000000000000, -379085775405950751413864142019127112262973828309/771445824682932916801210275945030502000000000000), (-3559822950830871356261101128739816432424067/3020668113835954351779614415211142000000000000, -748537531978193401787030912987859192578793/1519450761486898567293568619321500000000000), (379085775405950751413864142019127112262973828309/771445824682932916801210275945030502000000000000, -380903820477412686201112180219148057774414099819/771445824682932916801210275945030502000000000000), (748537531978193401787030912987859192578793/1519450761486898567293568619321500000000000, -3559822950830871356261101128739816432424067/3020668113835954351779614415211142000000000000), (380903820477412686201112180219148057774414099819/771445824682932916801210275945030502000000000000, 379085775405950751413864142019127112262973828309/771445824682932916801210275945030502000000000000), (3559822950830871356261101128739816432424067/3020668113835954351779614415211142000000000000, 748537531978193401787030912987859192578793/1519450761486898567293568619321500000000000), (-379085775405950751413864142019127112262973828309/771445824682932916801210275945030502000000000000, 380903820477412686201112180219148057774414099819/771445824682932916801210275945030502000000000000), (-748537531978193401787030912987859192578793/1519450761486898567293568619321500000000000, 3559822950830871356261101128739816432424067/3020668113835954351779614415211142000000000000)]

theorem terminal249Triangle0_vertex_pairs :
    ∀ v ∈ terminal249Triangle0Vertices, v ∈ pairwiseQDiff terminalPairOwner9 terminal249CoreField := by
  intro v hv
  simp only [terminal249Triangle0Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal249CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal249CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal249CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[4]'(by decide), terminal249CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 4 (by decide),
         List.getElem_mem terminal249CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal249CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner9[0]'(by decide), terminal249CoreField[2]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner9 0 (by decide),
         List.getElem_mem terminal249CoreField 2 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner9, terminal249CoreField]

theorem terminal249Triangle1_vertex_pairs :
    ∀ v ∈ terminal249Triangle1Vertices, v ∈ pairwiseQDiff terminalPairOwner13 terminal249CoreField := by
  intro v hv
  simp only [terminal249Triangle1Vertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[0]'(by decide), terminal249CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 0 (by decide),
         List.getElem_mem terminal249CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal249CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[1]'(by decide), terminal249CoreField[4]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 1 (by decide),
         List.getElem_mem terminal249CoreField 4 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal249CoreField]
  · apply List.mem_map.mpr
    refine ⟨(terminalPairOwner13[3]'(by decide), terminal249CoreField[6]'(by decide)), ?_, ?_⟩
    · exact List.mem_product.mpr
        ⟨List.getElem_mem terminalPairOwner13 3 (by decide),
         List.getElem_mem terminal249CoreField 6 (by decide)⟩
    · norm_num [qpointSub, terminalPairOwner13, terminal249CoreField]

end
end ElevenSquare.Tasks.T07
