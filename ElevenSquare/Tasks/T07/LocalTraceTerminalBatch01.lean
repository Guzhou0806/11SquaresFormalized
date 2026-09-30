import ElevenSquare.Tasks.T07.LocalTraceCover
import Mathlib.Tactic.Linarith

/-! Generated exact polygon union certificates from far15y-self-300.json.
The emitter is untrusted; each closed split and arithmetic leaf is checked
inside Lean.  Triangle-to-semantic forbidden-center bridges are separate. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal step 7, row 10; interval ['5/3968', '11/7936']. -/
def terminal10Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55690409 },
    { a := 25000000, b := 25000000, c := 81043089 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -100000000, b := 0, c := -49387829 },
    { a := 0, b := -100000000, c := -246130067 },
    { a := 100000000, b := -100000000, c := -193205021 } ]
def terminal10Cut : Halfplane := { a := -162307008265470899588798224906015604471073164000000000000, b := 252312954597865840419175849521670653569036726000000000000, c := 579293089551264605944231103679493881427693681720771209057 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal10Triangle0Vertices : List QPoint :=
  [(1306900666944118446280788236543374645174390799373/3076082395297669089549595411350652006000000000000, 7903170945052047053363353843991652048552356954739/3076082395297669089549595411350652006000000000000), (3332906134548825461623818693825768581464521/7821884059162699423494095238382000000000000, 8187185827410306666304860556595151422249/3942481884658618661035330261281250000000), (3830030212922776850472546731760081180864758059373/3076082395297669089549595411350652006000000000000, 9526241027706756049251336093051808093263088594739/3076082395297669089549595411350652006000000000000)]
def terminal10Triangle0 : Polygon :=
  [ { a := -11851721781537202069439636755003843646487414937638861960045860353514781864708202000000000000, b := -29868391985946101206785029539148620703988976125686628750883818738609735344640000000000000, c := -5112047106567885439135864002622012513400169357796903384870388799092044509803204420910759051 },
    { a := 24547187787957955332398176319866300913937220146664549256151171273414211671188202000000000000, b := -19705758382906941347278755510539328523524390289774845593610076563532218437975360000000000000, c := -30462556289910006584138299432993523194759547884853097703521912907794974273051358979740960949 },
    { a := -162307008265470899588798224906015604471073164000000000000, b := 252312954597865840419175849521670653569036726000000000000, c := 579293089551264605944231103679493881427693681720771209057 } ]
private theorem terminal10_leaf0 :
    Polygon.carrier (terminal10Cut :: terminal10Domain) ⊆ terminal10Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal10Triangle0, l.contains p
  intro l hl
  simp only [terminal10Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal10Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55690409 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs2 : ({ a := 25000000, b := 25000000, c := 81043089 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49387829 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -246130067 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193205021 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  simp only [Halfplane.contains, terminal10Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal10Triangle1Vertices : List QPoint :=
  [(975577616274395781293473253552134500986294279373/3076082395297669089549595411350652006000000000000, 11568217271053997580768325375037849337765830494739/3076082395297669089549595411350652006000000000000), (983596581318443706498242552939866242466135725261/3076082395297669089549595411350652006000000000000, 8537817500245347116858017270458183419808492179373/3076082395297669089549595411350652006000000000000), (2484916091787869784239124203017616318442388865261/3076082395297669089549595411350652006000000000000, 6226884300273493418263168068640239052226340879373/3076082395297669089549595411350652006000000000000)]
def terminal10Triangle1 : Polygon :=
  [ { a := -1239882402698707624115513554720828490182969052800000000, b := -3280944561092661374643055186393947268556390400000000, c := -405566574006433212265878963906700003669983212205755403 },
    { a := -2358095102012095610811070614099943232226685000000000000, b := -1531958684152475589531511887834438853036993000000000000, c := -5006042090261551794249392965252597401839264921148404529 },
    { a := 13144304255072726388719841496932671439610698798631419822426991562953570809016205059356800000000, b := 3714279610457935500463652113172009806693746427239101071058238657172396434748293193062400000000, c := 18136992246130529859299541623135213728408823366549735819624783669799607581095458047279209828231 } ]
private theorem terminal10_leaf1 :
    Polygon.carrier ((⟨-terminal10Cut.a, -terminal10Cut.b, -terminal10Cut.c⟩ : Halfplane) :: terminal10Domain) ⊆ terminal10Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal10Triangle1, l.contains p
  intro l hl
  simp only [terminal10Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal10Cut.a, -terminal10Cut.b, -terminal10Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55690409 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs2 : ({ a := 25000000, b := 25000000, c := 81043089 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49387829 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -246130067 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193205021 } : Halfplane).contains p :=
    hp _ (by simp [terminal10Domain])
  simp only [Halfplane.contains, terminal10Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal10_cover_cert :
    PolygonCoverCert [terminal10Triangle0, terminal10Triangle1] terminal10Domain := by
  refine PolygonCoverCert.split terminal10Domain terminal10Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal10Triangle0 (by simp) terminal10_leaf0
  · exact PolygonCoverCert.leaf _ terminal10Triangle1 (by simp) terminal10_leaf1
theorem terminal10_polygon_cover :
    terminal10Domain.carrier ⊆ ⋃ K ∈ [terminal10Triangle0, terminal10Triangle1], Polygon.carrier K :=
  terminal10_cover_cert.sound

/-- Archived far15 terminal step 7, row 11; interval ['11/7936', '3/1984']. -/
def terminal11Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55693257 },
    { a := 100000000, b := 100000000, c := 324183373 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -25000000, b := 25000000, c := 56237321 },
    { a := -100000000, b := 0, c := -49400211 },
    { a := -100000000, b := -100000000, c := -295517931 },
    { a := 0, b := -100000000, c := -246117719 },
    { a := 12500000, b := -12500000, c := -24150557 } ]
def terminal11Cut : Halfplane := { a := -649228476297237041591675719307669991211551532000000000000, b := 1009252507419144942594927950444090164386956038000000000000, c := 2317128677364137358543081070657847335026993190836219814873 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal11Triangle0Vertices : List QPoint :=
  [(5226083053917257646971711040862915989137579478309/12304337981496259406363256857627162678000000000000, 31611173711707803622496362314323126506696125730139/12304337981496259406363256857627162678000000000000), (4999364986294817096196673352108462407559581/11732830187209112148358009691974000000000000, 767503051855497754838778754987449251573/369607805796658018786479639994140625000), (15318608128108707072920990545303817633007139858309/12304337981496259406363256857627162678000000000000, 38103458474680174038413119507399826418811641050139/12304337981496259406363256857627162678000000000000)]
def terminal11Triangle0 : Polygon :=
  [ { a := -71110356657995953979364050080337557932697311300581195504248659440163504986874850000000000000, b := -197131468367457784924469879819914795134134385129553921697713907614962560125952000000000000, c := -30709509731219463596329056799464735462088166303683211728435391845365449956210388927041382351 },
    { a := 147283231308955937056715048264940488487020184435030385157833675310582983028554850000000000000, b := -118216751387270864257758312966529469651871280291492050503788353889463631829994048000000000000, c := -182723603383948666350770131601898020477930263785044408335189461996437232823354506372056257649 },
    { a := -649228476297237041591675719307669991211551532000000000000, b := 1009252507419144942594927950444090164386956038000000000000, c := 2317128677364137358543081070657847335026993190836219814873 } ]
private theorem terminal11_leaf0 :
    Polygon.carrier (terminal11Cut :: terminal11Domain) ⊆ terminal11Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal11Triangle0, l.contains p
  intro l hl
  simp only [terminal11Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal11Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55693257 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324183373 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs4 : ({ a := -25000000, b := 25000000, c := 56237321 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49400211 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517931 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246117719 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs8 : ({ a := 12500000, b := -12500000, c := -24150557 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  simp only [Halfplane.contains, terminal11Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs6 ⊢
    linarith only [hs1, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal11Triangle1Vertices : List QPoint :=
  [(3900789946446324814142780335416871720844552718309/12304337981496259406363256857627162678000000000000, 46271369024390653418892009900517419886865375750139/12304337981496259406363256857627162678000000000000), (3935920662162737414456547351619803893280627109861/12304337981496259406363256857627162678000000000000, 34149770133638435415055418767067588278932815418309/12304337981496259406363256857627162678000000000000), (9941202803911981257134298429085835113391571929861/12304337981496259406363256857627162678000000000000, 24906031022949628743007097646929049604844418518309/12304337981496259406363256857627162678000000000000)]
def terminal11Triangle1 : Polygon :=
  [ { a := -3099707040169530352693417744901190465903171690000000000000, b := -8983544812346196947698690190835882997159936000000000000, c := -1016469719475351821210725254527556262937199251555944610763 },
    { a := -66026707933491476228916579429560990529202835000000000000, b := -42894872441066027447698221981900223000792463000000000000, c := -140172183207082753077577724687188150268461710154075158559 },
    { a := 131443169929318091302197198110455673886135174661998812899901997020436932473973984820370000000000000, b := 37161640673016513836716394032976235196427002437518205098421476604186375710849200428128000000000000, c := 181419934032958086847286293680867046142771009166243743250869920926117961799504198011472757366490599 } ]
private theorem terminal11_leaf1 :
    Polygon.carrier ((⟨-terminal11Cut.a, -terminal11Cut.b, -terminal11Cut.c⟩ : Halfplane) :: terminal11Domain) ⊆ terminal11Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal11Triangle1, l.contains p
  intro l hl
  simp only [terminal11Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal11Cut.a, -terminal11Cut.b, -terminal11Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55693257 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324183373 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs4 : ({ a := -25000000, b := 25000000, c := 56237321 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49400211 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517931 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246117719 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  have hs8 : ({ a := 12500000, b := -12500000, c := -24150557 } : Halfplane).contains p :=
    hp _ (by simp [terminal11Domain])
  simp only [Halfplane.contains, terminal11Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs6 ⊢
    linarith only [hs4, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal11_cover_cert :
    PolygonCoverCert [terminal11Triangle0, terminal11Triangle1] terminal11Domain := by
  refine PolygonCoverCert.split terminal11Domain terminal11Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal11Triangle0 (by simp) terminal11_leaf0
  · exact PolygonCoverCert.leaf _ terminal11Triangle1 (by simp) terminal11_leaf1
theorem terminal11_polygon_cover :
    terminal11Domain.carrier ⊆ ⋃ K ∈ [terminal11Triangle0, terminal11Triangle1], Polygon.carrier K :=
  terminal11_cover_cert.sound

/-- Archived far15 terminal step 7, row 12; interval ['3/1984', '13/7936']. -/
def terminal12Domain : Polygon :=
  [ { a := 20000000, b := 0, c := 11139253 },
    { a := 100000000, b := 100000000, c := 324194393 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -50000000, b := 50000000, c := 112467779 },
    { a := -100000000, b := 0, c := -49412591 },
    { a := -100000000, b := -100000000, c := -295517959 },
    { a := 0, b := -100000000, c := -246105367 },
    { a := 12500000, b := -12500000, c := -24150457 } ]
def terminal12Cut : Halfplane := { a := -1623072401909898052984416677664379706126217440000000000, b := 2523133151356734625675476151178601883035326960000000000, c := 5792712729458307180561061918063435878457578271766986289 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal12Triangle0Vertices : List QPoint :=
  [(65307051954515368022083709776220001007215499537/153804339540361220431455531914727978800000000000, 395120815816943213047097825494397533526909790063/153804339540361220431455531914727978800000000000), (999874259325489725514450011084196380136527/2346566931652381632533463793173200000000000, 61396596542469010992993523097401688227/29568635731506825006722074006718750000), (191463709522352099305857517335150095158981847537/153804339540361220431455531914727978800000000000, 476274435912438115696318659377616518833220662063/153804339540361220431455531914727978800000000000)]
def terminal12Triangle0 : Polygon :=
  [ { a := -177775962212306437729975655331277478477147520263750819954627933569363755565975600000000000, b := -537631558795008229209720194302804586277601351640676232050051395551322400819200000000000, c := -76866839101640798884634761598273149896358690651427362397933187042086611023453196360586561 },
    { a := 122736121170758323176533678493914272115135209609683241969673476812891431532125200000000000, b := -98499136432561280275832520017361623450411871231076280025374990188457524357593600000000000, c := -152226573453722832518618413107398311701320516330722631797062438886235104062927284166809813 },
    { a := -1623072401909898052984416677664379706126217440000000000, b := 2523133151356734625675476151178601883035326960000000000, c := 5792712729458307180561061918063435878457578271766986289 } ]
private theorem terminal12_leaf0 :
    Polygon.carrier (terminal12Cut :: terminal12Domain) ⊆ terminal12Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal12Triangle0, l.contains p
  intro l hl
  simp only [terminal12Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal12Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 20000000, b := 0, c := 11139253 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324194393 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112467779 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49412591 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517959 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246105367 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs8 : ({ a := 12500000, b := -12500000, c := -24150457 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  simp only [Halfplane.contains, terminal12Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs7 ⊢
    linarith only [hs1, hs7]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal12Triangle1Vertices : List QPoint :=
  [(48740875749139994378919484677893160952895203537/153804339540361220431455531914727978800000000000, 578373393971960023361582045385942734477359282063/153804339540361220431455531914727978800000000000), (49218195430470709926483965276183513978368073937/153804339540361220431455531914727978800000000000, 426853410243645179561182613327624253880022623537/153804339540361220431455531914727978800000000000), (124284278218043000561332897070100544565769645937/153804339540361220431455531914727978800000000000, 311306585136845742623616956031886988882303883537/153804339540361220431455531914727978800000000000)]
def terminal12Triangle1 : Polygon :=
  [ { a := -38746352150161969424038153619175080969853109200000000000, b := -122059123859230664534403110127528123975680000000000000, c := -12737786797628439315738502771677321889082802353542184383 },
    { a := -825334465048567406696897552112409035697991000000000000, b := -536186305625516361677492369956550218481439800000000000, c := -1752190002465671080545821254301710407793524067751551267 },
    { a := 20538017073018329348619868207444501306479049924798956379103954708071987636858239624400000000000, b := 5809451561680660037320033847491620412048962104535578392215950932330897377364510560000000000000, c := 28354682112140402169904161961115295470906120131576453070653421639840069268462491933524433228831 } ]
private theorem terminal12_leaf1 :
    Polygon.carrier ((⟨-terminal12Cut.a, -terminal12Cut.b, -terminal12Cut.c⟩ : Halfplane) :: terminal12Domain) ⊆ terminal12Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal12Triangle1, l.contains p
  intro l hl
  simp only [terminal12Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal12Cut.a, -terminal12Cut.b, -terminal12Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 20000000, b := 0, c := 11139253 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324194393 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112467779 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49412591 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517959 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246105367 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  have hs8 : ({ a := 12500000, b := -12500000, c := -24150457 } : Halfplane).contains p :=
    hp _ (by simp [terminal12Domain])
  simp only [Halfplane.contains, terminal12Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs6 ⊢
    linarith only [hs4, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal12_cover_cert :
    PolygonCoverCert [terminal12Triangle0, terminal12Triangle1] terminal12Domain := by
  refine PolygonCoverCert.split terminal12Domain terminal12Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal12Triangle0 (by simp) terminal12_leaf0
  · exact PolygonCoverCert.leaf _ terminal12Triangle1 (by simp) terminal12_leaf1
theorem terminal12_polygon_cover :
    terminal12Domain.carrier ⊆ ⋃ K ∈ [terminal12Triangle0, terminal12Triangle1], Polygon.carrier K :=
  terminal12_cover_cert.sound

/-- Archived far15 terminal step 7, row 13; interval ['13/7936', '7/3968']. -/
def terminal13Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55699201 },
    { a := 12500000, b := 12500000, c := 40525677 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -100000000, b := 0, c := -49424967 },
    { a := 0, b := -100000000, c := -246093013 },
    { a := 25000000, b := -25000000, c := -48300741 } ]
def terminal13Cut : Halfplane := { a := -129845897292419257684417452871714908710164674400000000000, b := 201850815552436365749031189007859025564694519600000000000, c := 463408320291681164407394849075418451261430704681577534493 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal13Triangle0Vertices : List QPoint :=
  [(1044609194992821832212164656929581846547196193049/2460871425277893142543169575786847207600000000000, 6321631688201404123180703810207174937620181199719/2460871425277893142543169575786847207600000000000), (3332918755214088524374972100450807567710629/7821893001268291452112713786166000000000000, 8185726785021982908661349635957450662713/3942486391768292062556811384156250000000), (3063117350517185489702476547008172102194141389049/2460871425277893142543169575786847207600000000000, 7620090661125596700024878338924324024721827943719/2460871425277893142543169575786847207600000000000)]
def terminal13Triangle0 : Polygon :=
  [ { a := -9481388715999750349956521629364839213794852387161083538763548630581841620693254800000000000, b := -31063176104258421347052602807967117068670786495233185551604098452557111929446400000000000, c := -4104528049973502502519025504576051032139589023999712156362156688265555036674672483029550243 },
    { a := 19637795868749506213704739582548627754754320866440706127803098038391527764197254800000000000, b := -15757491638594729640302166239165045993338604621523275655457381548360507846606553600000000000, c := -24349358934822260050772825418807710284350295166372884419799402035306824747624215831596505757 },
    { a := -129845897292419257684417452871714908710164674400000000000, b := 201850815552436365749031189007859025564694519600000000000, c := 463408320291681164407394849075418451261430704681577534493 } ]
private theorem terminal13_leaf0 :
    Polygon.carrier (terminal13Cut :: terminal13Domain) ⊆ terminal13Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal13Triangle0, l.contains p
  intro l hl
  simp only [terminal13Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal13Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55699201 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs2 : ({ a := 12500000, b := 12500000, c := 40525677 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49424967 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -246093013 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs6 : ({ a := 25000000, b := -25000000, c := -48300741 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  simp only [Halfplane.contains, terminal13Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal13Triangle1Vertices : List QPoint :=
  [(779550161081566623006862536959934490187980601049/2460871425277893142543169575786847207600000000000, 9253675312834269990217855449292100560063167683719/2460871425277893142543169575786847207600000000000), (787798248449037547665453759878386316710549528281/2460871425277893142543169575786847207600000000000, 6829355611679740277372390731964968139955297941049/2460871425277893142543169575786847207600000000000), (1988856545578587433401055272578285938047190172281/2460871425277893142543169575786847207600000000000, 4980604912989036928050465844055226197702172961049/2460871425277893142543169575786847207600000000000)]
def terminal13Triangle1 : Polygon :=
  [ { a := -619941880455365119596341102138718902076305378000000000000, b := -2109183368148578877756040125371997299467468800000000000, c := -204315221701389189324779714234694313475580378426660068367 },
    { a := -13205362133505023923728034913641013873236607000000000000, b := -8578987836639642040968582233570711580976004600000000000, c := -28035645899625480824002008163691500244990124453788813499 },
    { a := 5257738422589957713437083806064350261068264408141842301436051678902843002970612958146000000000000, b := 1487973763007419730707403763764590997810483629744421347198979854824726857733546245881600000000000, c := 7260800677192587383670382530398727971038495687886182767231926385898595103503209829368972121626319 } ]
private theorem terminal13_leaf1 :
    Polygon.carrier ((⟨-terminal13Cut.a, -terminal13Cut.b, -terminal13Cut.c⟩ : Halfplane) :: terminal13Domain) ⊆ terminal13Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal13Triangle1, l.contains p
  intro l hl
  simp only [terminal13Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal13Cut.a, -terminal13Cut.b, -terminal13Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55699201 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs2 : ({ a := 12500000, b := 12500000, c := 40525677 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49424967 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -246093013 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  have hs6 : ({ a := 25000000, b := -25000000, c := -48300741 } : Halfplane).contains p :=
    hp _ (by simp [terminal13Domain])
  simp only [Halfplane.contains, terminal13Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal13_cover_cert :
    PolygonCoverCert [terminal13Triangle0, terminal13Triangle1] terminal13Domain := by
  refine PolygonCoverCert.split terminal13Domain terminal13Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal13Triangle0 (by simp) terminal13_leaf0
  · exact PolygonCoverCert.leaf _ terminal13Triangle1 (by simp) terminal13_leaf1
theorem terminal13_polygon_cover :
    terminal13Domain.carrier ⊆ ⋃ K ∈ [terminal13Triangle0, terminal13Triangle1], Polygon.carrier K :=
  terminal13_cover_cert.sound

/-- Archived far15 terminal step 7, row 14; interval ['7/3968', '15/7936']. -/
def terminal14Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55702143 },
    { a := 50000000, b := 50000000, c := 162108221 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -5000000, b := 0, c := -2471867 },
    { a := 0, b := -6250000, c := -15380041 },
    { a := 20000000, b := -20000000, c := -38640453 } ]
def terminal14Cut : Halfplane := { a := -162307513347924580576030103426713158784714348000000000000, b := 252313739769421681984615227953927141736489382000000000000, c := 579249551596295300357621448997981231160118080912159223241 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal14Triangle0Vertices : List QPoint :=
  [(186483161056490066399186955834012011491881759171/439441709677818312536582514993062906000000000000, 7901663309629621122249374947367591079323278951979/3076091967744728187756077604951440342000000000000), (9998770989751739146334595275748301520419013/23465689436261398389726529664246000000000000, 24555722873610961141200839166333406142353/11827464433599495156112162129156250000000), (546931360727092469234351567196765071115438019171/439441709677818312536582514993062906000000000000, 9524738443108866928009675981634722667170422431979/3076091967744728187756077604951440342000000000000)]
def terminal14Triangle0 : Polygon :=
  [ { a := -35555224056608616583253220188134647300660687383108789117602839834882699441866450000000000000, b := -125447531786947072829804631151324239453803563219556112850150464641768482921984000000000000, c := -15410591970368341127186996770979728555210139481972439131918284873238084405689088116612663383 },
    { a := 73641801070551114039026671166450208703208105360417307334718779561377287457946450000000000000, b := -59081711047522311367743620817798468960561326401777713675283486356470271876798016000000000000, c := -91284257487101006953707782859672579643762927736180702018932014720041182474979996669986736617 },
    { a := -162307513347924580576030103426713158784714348000000000000, b := 252313739769421681984615227953927141736489382000000000000, c := 579249551596295300357621448997981231160118080912159223241 } ]
private theorem terminal14_leaf0 :
    Polygon.carrier (terminal14Cut :: terminal14Domain) ⊆ terminal14Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal14Triangle0, l.contains p
  intro l hl
  simp only [terminal14Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal14Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55702143 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs2 : ({ a := 50000000, b := 50000000, c := 162108221 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs4 : ({ a := -5000000, b := 0, c := -2471867 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs5 : ({ a := 0, b := -6250000, c := -15380041 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs6 : ({ a := 20000000, b := -20000000, c := -38640453 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  simp only [Halfplane.contains, terminal14Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal14Triangle1Vertices : List QPoint :=
  [(139151149383283869090492924361967901863107239171/439441709677818312536582514993062906000000000000, 11566721040872854661863800727036845867754110731979/3076091967744728187756077604951440342000000000000), (985131871433020516327666630146392513554083808021/3076091967744728187756077604951440342000000000000, 1219474494650634021394017991417033502401490139171/439441709677818312536582514993062906000000000000), (2486456053851921916598629051828947330524952788021/3076091967744728187756077604951440342000000000000, 889340153028555268754338189247991803581143839171/439441709677818312536582514993062906000000000000)]
def terminal14Triangle1 : Polygon :=
  [ { a := -1239884292384356265149966825139042221037445929600000000, b := -4530842302877713433874782235609243430843187200000000, c := -409651685620566076859266483628954102956341404807763891 },
    { a := -16506717081103937631983990108452084941017315000000000000, b := -10723744160135010001935445869161105835506207000000000000, c := -35045317777499139234336236242713965349011336459305401007 },
    { a := 13144362382163908994164935897393870729758725617645985295903223678600917573938900353155200000000, b := 3721820291969268997136179933014030025372215789307758979372651191055066396902263590246400000000, c := 18157008828359912442524647337380251838481488309769495468840637907935835171402685262297742255863 } ]
private theorem terminal14_leaf1 :
    Polygon.carrier ((⟨-terminal14Cut.a, -terminal14Cut.b, -terminal14Cut.c⟩ : Halfplane) :: terminal14Domain) ⊆ terminal14Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal14Triangle1, l.contains p
  intro l hl
  simp only [terminal14Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal14Cut.a, -terminal14Cut.b, -terminal14Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55702143 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs2 : ({ a := 50000000, b := 50000000, c := 162108221 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs4 : ({ a := -5000000, b := 0, c := -2471867 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs5 : ({ a := 0, b := -6250000, c := -15380041 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  have hs6 : ({ a := 20000000, b := -20000000, c := -38640453 } : Halfplane).contains p :=
    hp _ (by simp [terminal14Domain])
  simp only [Halfplane.contains, terminal14Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal14_cover_cert :
    PolygonCoverCert [terminal14Triangle0, terminal14Triangle1] terminal14Domain := by
  refine PolygonCoverCert.split terminal14Domain terminal14Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal14Triangle0 (by simp) terminal14_leaf0
  · exact PolygonCoverCert.leaf _ terminal14Triangle1 (by simp) terminal14_leaf1
theorem terminal14_polygon_cover :
    terminal14Domain.carrier ⊆ ⋃ K ∈ [terminal14Triangle0, terminal14Triangle1], Polygon.carrier K :=
  terminal14_cover_cert.sound

/-- Archived far15 terminal step 7, row 15; interval ['15/7936', '1/496']. -/
def terminal15Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55705091 },
    { a := 10000000, b := 10000000, c := 32422747 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -50000000, b := 50000000, c := 112447201 },
    { a := -100000000, b := 0, c := -49449709 },
    { a := -20000000, b := -20000000, c := -59103601 },
    { a := 0, b := -20000000, c := -49213659 },
    { a := 2500000, b := -2500000, c := -4830039 } ]
def terminal15Cut : Halfplane := { a := -675578211813547689525713255662590037999436000000000000, b := 1050214260654830909099597668331145557729174000000000000, c := 2410983253443754568250211508710909911068624603469551153 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal15Triangle0Vertices : List QPoint :=
  [(5431854068751298286378258619268999711015298717/12803724658687057543714460144365894000000000000, 32887772796822015426224945511823181256725442531/12803724658687057543714460144365894000000000000), (1249848345697914746846692129253700031653331/2933212576736673553187475356122000000000000, 396036551171332929723351290553932866991/190765646249783659806677637625000000000), (15933996675299607377374235302580455288307038717/12803724658687057543714460144365894000000000000, 39643554914957492321482078068449081636719802531/12803724658687057543714460144365894000000000000)]
def terminal15Triangle0 : Polygon :=
  [ { a := -18499085097443830130822850127289893770162287832867342770946679756399005052078000000000000, b := -69931413972037010638788883803690009761403641699196464368690029561643197440000000000000, c := -8027681151286138110704046879403578330508038107907333280379334126493575647944143971610089 },
    { a := 12771743390683844883091925418114195195582377645835733025525365840583492324026000000000000, b := -10245028454079177958884418379500373614149224921773746435859494007742463027520000000000000, c := -15826990723528552041366305741903580119766354679578480696398924815099351306993315582356637 },
    { a := -675578211813547689525713255662590037999436000000000000, b := 1050214260654830909099597668331145557729174000000000000, c := 2410983253443754568250211508710909911068624603469551153 } ]
private theorem terminal15_leaf0 :
    Polygon.carrier (terminal15Cut :: terminal15Domain) ⊆ terminal15Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal15Triangle0, l.contains p
  intro l hl
  simp only [terminal15Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal15Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55705091 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs2 : ({ a := 10000000, b := 10000000, c := 32422747 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112447201 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49449709 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs6 : ({ a := -20000000, b := -20000000, c := -59103601 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs7 : ({ a := 0, b := -20000000, c := -49213659 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs8 : ({ a := 2500000, b := -2500000, c := -4830039 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  simp only [Halfplane.contains, terminal15Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs6 ⊢
    linarith only [hs1, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal15Triangle1Vertices : List QPoint :=
  [(4052772311924417356838149471506233000493818717/12803724658687057543714460144365894000000000000, 48142970151482139067910645559261576327312902531/12803724658687057543714460144365894000000000000), (4102044084334223348780489369007066723943877469/12803724658687057543714460144365894000000000000, 35529444531537049081835637990354296282030918717/12803724658687057543714460144365894000000000000), (10351057981410031178221789521734001110891737469/12803724658687057543714460144365894000000000000, 25910536909852565327778151048265184086137218717/12803724658687057543714460144365894000000000000)]
def terminal15Triangle1 : Polygon :=
  [ { a := -134256271728088053027277589024980342033680000000000, b := -524440562019821876990544287513227018240000000000, c := -44468171743996809983166540718469691664304781284891 },
    { a := -68706483012032026814696335300636515684955000000000000, b := -44635813550541484496009286805192388478199000000000000, c := -145873387131275018495708324351929861472144253610497287 },
    { a := 5693159074369328127447068637418933552762272907117748905906181694634832897388794320000000000, b := 1612830310676965530856081795670853013164374007965159553111085804996803127436885760000000000, c := 7866423377198759269099118072740822023712978571532621597302982097628214187563919457025206159 } ]
private theorem terminal15_leaf1 :
    Polygon.carrier ((⟨-terminal15Cut.a, -terminal15Cut.b, -terminal15Cut.c⟩ : Halfplane) :: terminal15Domain) ⊆ terminal15Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal15Triangle1, l.contains p
  intro l hl
  simp only [terminal15Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal15Cut.a, -terminal15Cut.b, -terminal15Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55705091 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs2 : ({ a := 10000000, b := 10000000, c := 32422747 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112447201 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49449709 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs6 : ({ a := -20000000, b := -20000000, c := -59103601 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs7 : ({ a := 0, b := -20000000, c := -49213659 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  have hs8 : ({ a := 2500000, b := -2500000, c := -4830039 } : Halfplane).contains p :=
    hp _ (by simp [terminal15Domain])
  simp only [Halfplane.contains, terminal15Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs6 ⊢
    linarith only [hs4, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs4 ⊢
    linarith only [hs1, hs4]
theorem terminal15_cover_cert :
    PolygonCoverCert [terminal15Triangle0, terminal15Triangle1] terminal15Domain := by
  refine PolygonCoverCert.split terminal15Domain terminal15Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal15Triangle0 (by simp) terminal15_leaf0
  · exact PolygonCoverCert.leaf _ terminal15Triangle1 (by simp) terminal15_leaf1
theorem terminal15_polygon_cover :
    terminal15Domain.carrier ⊆ ⋃ K ∈ [terminal15Triangle0, terminal15Triangle1], Polygon.carrier K :=
  terminal15_cover_cert.sound

/-- Archived far15 terminal step 7, row 16; interval ['1/496', '43/7936']. -/
def terminal16Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28017931 },
    { a := 20000000, b := 20000000, c := 64883351 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -25000000, b := 0, c := -12365519 },
    { a := -12500000, b := -12500000, c := -36930719 },
    { a := 0, b := -4000000, c := -9839347 },
    { a := 100000000, b := -100000000, c := -192864867 } ]
def terminal16Cut : Halfplane := { a := -2544376840406006986155183703951601603440748000000000000, b := 3955338990434687700512171434100828832226982000000000000, c := 9067361655278153788643529327124814297315065165835281769 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal16Triangle0Vertices : List QPoint :=
  [(20452226348532306278594098034178157860913677173/48221656534846471570383197816905942000000000000, 123701501099463461637030969988147867494379360011/48221656534846471570383197816905942000000000000), (1249886145396128616898862578045457666227583/2933233441649721619964251967618000000000000, 12266941767840302930151030070090582352469/5913777100100245201540830579875000000000), (60005616252879183283715812375186446183183497173/48221656534846471570383197816905942000000000000, 149145269503523531498582807027663883528786840011/48221656534846471570383197816905942000000000000)]
def terminal16Triangle0 : Polygon :=
  [ { a := -69445382486984326245862167016644341003225997908243163825134575634163158607990000000000000, b := -280426129250756945408643731382180868905560307148630471384304497303375214272000000000000, c := -30173202647416435440520602945718336937296607337612667314982776629600955355189619732275461 },
    { a := 144077894851363889762043414086867345128048637491342841916046545812940141247990000000000000, b := -115738899868789986513658239155502572593223536039960500974649201525595313545728000000000000, c := -178683752553624728937985860242943451782293521464742996164439777007952919696601290794564539 },
    { a := -2544376840406006986155183703951601603440748000000000000, b := 3955338990434687700512171434100828832226982000000000000, c := 9067361655278153788643529327124814297315065165835281769 } ]
private theorem terminal16_leaf0 :
    Polygon.carrier (terminal16Cut :: terminal16Domain) ⊆ terminal16Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal16Triangle0, l.contains p
  intro l hl
  simp only [terminal16Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal16Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 50000000, b := 0, c := 28017931 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs2 : ({ a := 20000000, b := 20000000, c := 64883351 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs4 : ({ a := -25000000, b := 0, c := -12365519 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs5 : ({ a := -12500000, b := -12500000, c := -36930719 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs6 : ({ a := 0, b := -4000000, c := -9839347 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs7 : ({ a := 100000000, b := -100000000, c := -192864867 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  simp only [Halfplane.contains, terminal16Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal16Triangle1Vertices : List QPoint :=
  [(15258299691724783036701634619573952653540037173/48221656534846471570383197816905942000000000000, 181155945553531668446055813301154417653915140011/48221656534846471570383197816905942000000000000), (15610323582721673752395068805413893258951399989/48221656534846471570383197816905942000000000000, 133806403239411561549066638498536284549260337173/48221656534846471570383197816905942000000000000), (39145490876546653980809031471136226335484379989/48221656534846471570383197816905942000000000000, 97579471472444776844484334362244361075956237173/48221656534846471570383197816905942000000000000)]
def terminal16Triangle1 : Polygon :=
  [ { a := -485914014871529387939539268690852238037505040000000000, b := -3612565905499512688731376386339674845921280000000000, c := -167324393967543572746350211076365289446191408047723083 },
    { a := -258763798335477033604159315259228024809315000000000000, b := -168108337813035573060099733326588093403807000000000000, c := -550237394720261362269675960424567174508212616549992463 },
    { a := 80603920550633409229663545657910121654308033815008774864934873108832540923257267920000000000, b := 23037598577933852057445621019346070326311166785672759020829822425292290233508253440000000000, c := 112050831888225698326437977268263330775917556800503952526796160630707239260024479928936744159 } ]
private theorem terminal16_leaf1 :
    Polygon.carrier ((⟨-terminal16Cut.a, -terminal16Cut.b, -terminal16Cut.c⟩ : Halfplane) :: terminal16Domain) ⊆ terminal16Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal16Triangle1, l.contains p
  intro l hl
  simp only [terminal16Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal16Cut.a, -terminal16Cut.b, -terminal16Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 50000000, b := 0, c := 28017931 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs2 : ({ a := 20000000, b := 20000000, c := 64883351 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs4 : ({ a := -25000000, b := 0, c := -12365519 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs5 : ({ a := -12500000, b := -12500000, c := -36930719 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs6 : ({ a := 0, b := -4000000, c := -9839347 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  have hs7 : ({ a := 100000000, b := -100000000, c := -192864867 } : Halfplane).contains p :=
    hp _ (by simp [terminal16Domain])
  simp only [Halfplane.contains, terminal16Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal16_cover_cert :
    PolygonCoverCert [terminal16Triangle0, terminal16Triangle1] terminal16Domain := by
  refine PolygonCoverCert.split terminal16Domain terminal16Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal16Triangle0 (by simp) terminal16_leaf0
  · exact PolygonCoverCert.leaf _ terminal16Triangle1 (by simp) terminal16_leaf1
theorem terminal16_polygon_cover :
    terminal16Domain.carrier ⊆ ⋃ K ∈ [terminal16Triangle0, terminal16Triangle1], Polygon.carrier K :=
  terminal16_cover_cert.sound

/-- Archived far15 terminal step 7, row 17; interval ['43/7936', '35/3968']. -/
def terminal17Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 56119419 },
    { a := 100000000, b := 100000000, c := 324468427 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -50000000, b := 0, c := -24897391 },
    { a := 0, b := -25000000, c := -61511597 },
    { a := 100000000, b := -100000000, c := -192841121 } ]
def terminal17Cut : Halfplane := { a := -130280178626708879364560640668639419540443541600000000000, b := 202525923841057497301543639651578884228859924400000000000, c := 464024361189646220827748392415446017570484058925334748821 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal17Triangle0Vertices : List QPoint :=
  [(1039060252863996143265951223184345918351424835633/2469102032084653455799223251067559556400000000000, 6325572668428244039899980596562347109693340074063/2469102032084653455799223251067559556400000000000), (10000310210069931794450930215336183249131613/23466732681913801728565360239046000000000000, 24495142870941095714713308735792175601841/11827990263061392000284959797906250000000), (3064319491274571116281387619700134760640024079633/2469102032084653455799223251067559556400000000000, 7628374454695332833545587003248741305097775490063/2469102032084653455799223251067559556400000000000)]
def terminal17Triangle0 : Polygon :=
  [ { a := -28446204904958140348301099312945907172861939760049945652627453482867343553532416400000000000, b := -308437066799419075539138453471425935231813361280876797530227368782131320770355200000000000, c := -12761061119309453730516617869840071816453481294479725962554727778831710103047976123889153267 },
    { a := 59018706160807712461142221047272798430623789922792567605702290772305772006668416400000000000, b := -47217780092557876532575444381095492344245746495554433051726008325526203560453644800000000000, c := -72634801436578243883734607905932460638482348586578115813564745912257520205160971628381574733 },
    { a := -130280178626708879364560640668639419540443541600000000000, b := 202525923841057497301543639651578884228859924400000000000, c := 464024361189646220827748392415446017570484058925334748821 } ]
private theorem terminal17_leaf0 :
    Polygon.carrier (terminal17Cut :: terminal17Domain) ⊆ terminal17Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal17Triangle0, l.contains p
  intro l hl
  simp only [terminal17Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal17Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 56119419 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324468427 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs4 : ({ a := -50000000, b := 0, c := -24897391 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs5 : ({ a := 0, b := -25000000, c := -61511597 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -192841121 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  simp only [Halfplane.contains, terminal17Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs6 ⊢
    linarith only [hs1, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal17Triangle1Vertices : List QPoint :=
  [(773114705067336728640821250361344697716123547633/2469102032084653455799223251067559556400000000000, 9267422777856184599559341048937275086419604350063/2469102032084653455799223251067559556400000000000), (807635398939519804092201308486955470728037117937/2469102032084653455799223251067559556400000000000, 6843154276558537554748922161057695237524038807633/2469102032084653455799223251067559556400000000000), (2012710744052206035120638408701908425780049633937/2469102032084653455799223251067559556400000000000, 4988220264132567322292708610334394493144331587633/2469102032084653455799223251067559556400000000000)]
def terminal17Triangle1 : Polygon :=
  [ { a := -621985604094098530151890248028975131723181986000000000000, b := -8856846764433962041000631345653412993094860800000000000, c := -227996394233551349517721997434937760213357972944757110831 },
    { a := -13249528660185501660401525362309291031283623000000000000, b := -8607681036519187364488836430106806821800089400000000000, c := -28190199010435719199189964795624030820230465483327716483 },
    { a := 5282893811168370293270388411282231822720944797550564740481613389697450755424386693026000000000000, b := 1530344549410814055189422584226039302326937911825792387242394884216759265768543177772800000000000, c := 7398087478174760564402740000111976240661373689107922472590141604054447382647759214090384381832671 } ]
private theorem terminal17_leaf1 :
    Polygon.carrier ((⟨-terminal17Cut.a, -terminal17Cut.b, -terminal17Cut.c⟩ : Halfplane) :: terminal17Domain) ⊆ terminal17Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal17Triangle1, l.contains p
  intro l hl
  simp only [terminal17Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal17Cut.a, -terminal17Cut.b, -terminal17Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 56119419 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324468427 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs4 : ({ a := -50000000, b := 0, c := -24897391 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs5 : ({ a := 0, b := -25000000, c := -61511597 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -192841121 } : Halfplane).contains p :=
    hp _ (by simp [terminal17Domain])
  simp only [Halfplane.contains, terminal17Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal17_cover_cert :
    PolygonCoverCert [terminal17Triangle0, terminal17Triangle1] terminal17Domain := by
  refine PolygonCoverCert.split terminal17Domain terminal17Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal17Triangle0 (by simp) terminal17_leaf0
  · exact PolygonCoverCert.leaf _ terminal17Triangle1 (by simp) terminal17_leaf1
theorem terminal17_polygon_cover :
    terminal17Domain.carrier ⊆ ⋃ K ∈ [terminal17Triangle0, terminal17Triangle1], Polygon.carrier K :=
  terminal17_cover_cert.sound

/-- Archived far15 terminal step 7, row 18; interval ['35/3968', '97/7936']. -/
def terminal18Domain : Polygon :=
  [ { a := 2000000, b := 0, c := 1124141 },
    { a := 153779168187480465496513805430175240500000000, b := 3236386648977153697066134574629171200000000, c := 95007250812624534487067353841426578838485983 },
    { a := 100000000, b := 100000000, c := 324518147 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -10000000, b := 0, c := -5012517 },
    { a := -100000000, b := -100000000, c := -296354307 },
    { a := 0, b := -6250000, c := -15389321 },
    { a := 3125000, b := -3125000, c := -6025399 } ]
def terminal18Cut : Halfplane := { a := -162867856384861728196085212081709191861123436000000000000, b := 253184816186570024396180583410423679361595174000000000000, c := 579767119373937967595737940827407363750990795004807677449 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal18Triangle0Vertices : List QPoint :=
  [(1288837966367979974610355371570457071361309364117/3086711726987845738647788537842711894000000000000, 7897330784757126972006122516837370867198574019307/3086711726987845738647788537842711894000000000000), (10002297960838843425804466758779823582893623/23468141063544546235997781515026000000000000, 24456971166402620576704337112899352560619/11828700132834952739918236650718750000000), (3820686128233680218572161205674693864977261104117/3086711726987845738647788537842711894000000000000, 9526009348605744253966974637654462785809808379307/3086711726987845738647788537842711894000000000000)]
def terminal18Triangle0 : Polygon :=
  [ { a := -35560299385571063185192266204418774598651527803752361244122306545078141826673158000000000000, b := -627579209772238542097077742641686851681451643747556066923579827262961098129920000000000000, c := -16453646808898707704457907862031509912561148296759341164961837866366724796879775982086868029 },
    { a := 73782357669141556517343226035211965230750148597844383191150359650702889320033158000000000000, b := -58790190604367980431133964494583052985779606814716153116574695884675139747110080000000000000, c := -90107758498094800704625213305633063375878374214103629273243779389199812441434616813113891971 },
    { a := -162867856384861728196085212081709191861123436000000000000, b := 253184816186570024396180583410423679361595174000000000000, c := 579767119373937967595737940827407363750990795004807677449 } ]
private theorem terminal18_leaf0 :
    Polygon.carrier (terminal18Cut :: terminal18Domain) ⊆ terminal18Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal18Triangle0, l.contains p
  intro l hl
  simp only [terminal18Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal18Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 2000000, b := 0, c := 1124141 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs2 : ({ a := 153779168187480465496513805430175240500000000, b := 3236386648977153697066134574629171200000000, c := 95007250812624534487067353841426578838485983 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs3 : ({ a := 100000000, b := 100000000, c := 324518147 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs4 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs5 : ({ a := -10000000, b := 0, c := -5012517 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -296354307 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs7 : ({ a := 0, b := -6250000, c := -15389321 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs8 : ({ a := 3125000, b := -3125000, c := -6025399 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  simp only [Halfplane.contains, terminal18Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs6 ⊢
    linarith only [hs1, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal18Triangle1Vertices : List QPoint :=
  [(956370036546920763051130483876770522031467884117/3086711726987845738647788537842711894000000000000, 11575041593712619517833095689273374921183301479307/3086711726987845738647788537842711894000000000000), (1020144761605182563318150940802829199339975300693/3086711726987845738647788537842711894000000000000, 8544741065824736281196845298583305197291904984117/3086711726987845738647788537842711894000000000000), (2526652046977552657904758253239241041864663160693/3086711726987845738647788537842711894000000000000, 6225822489539851423956628720936969331737711284117/3086711726987845738647788537842711894000000000000)]
def terminal18Triangle1 : Polygon :=
  [ { a := -777519518256727297783109381029602616545835530000000000000, b := -16363424369270863246315111690661600742643712000000000000, c := -302264600747630892365926733010846099591132048443175277051 },
    { a := -16563704116320606123144404126045256182529955000000000000, b := -10760766324088357818475766517402941732319199000000000000, c := -35262553656878286218407610014188865230160571551817824367 },
    { a := 8255748669538751051198784592953142120136738103008839318346910748648777130183197294930000000000000, b := 2423503948137141085956736919422977362989248913004808233051075294812136982453607397472000000000000, c := 11645956227374217299840174089501986571630301360204135906778693232945788766757471113647948068305031 } ]
private theorem terminal18_leaf1 :
    Polygon.carrier ((⟨-terminal18Cut.a, -terminal18Cut.b, -terminal18Cut.c⟩ : Halfplane) :: terminal18Domain) ⊆ terminal18Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal18Triangle1, l.contains p
  intro l hl
  simp only [terminal18Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal18Cut.a, -terminal18Cut.b, -terminal18Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 2000000, b := 0, c := 1124141 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs2 : ({ a := 153779168187480465496513805430175240500000000, b := 3236386648977153697066134574629171200000000, c := 95007250812624534487067353841426578838485983 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs3 : ({ a := 100000000, b := 100000000, c := 324518147 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs4 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs5 : ({ a := -10000000, b := 0, c := -5012517 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -296354307 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs7 : ({ a := 0, b := -6250000, c := -15389321 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  have hs8 : ({ a := 3125000, b := -3125000, c := -6025399 } : Halfplane).contains p :=
    hp _ (by simp [terminal18Domain])
  simp only [Halfplane.contains, terminal18Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal18_cover_cert :
    PolygonCoverCert [terminal18Triangle0, terminal18Triangle1] terminal18Domain := by
  refine PolygonCoverCert.split terminal18Domain terminal18Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal18Triangle0 (by simp) terminal18_leaf0
  · exact PolygonCoverCert.leaf _ terminal18Triangle1 (by simp) terminal18_leaf1
theorem terminal18_polygon_cover :
    terminal18Domain.carrier ⊆ ⋃ K ∈ [terminal18Triangle0, terminal18Triangle1], Polygon.carrier K :=
  terminal18_cover_cert.sound

/-- Archived far15 terminal step 7, row 19; interval ['97/7936', '1/64']. -/
def terminal19Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 56298751 },
    { a := 123021907993758149169612758617956963300000000, b := 3426551628602214780095587922430054400000000, c := 78214798288046151217638325416097716857454339 },
    { a := 6250000, b := 6250000, c := 20030933 },
    { a := -50000000, b := 0, c := -25226609 },
    { a := 0, b := -50000000, c := -123209319 },
    { a := 10000000, b := -10000000, c := -19277981 } ]
def terminal19Cut : Halfplane := { a := -130314414650303541700970923378961773241692424800000000000, b := 202579145155153329760120752279807199229673473200000000000, c := 463616903947601383463259992164726477396542698768146061893 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal19Triangle0Vertices : List QPoint :=
  [(1023183803063226594213493849799498301169263046177/2469750881635821854892181682505408369200000000000, 6310392190976204008895140236533032360835760994911/2469750881635821854892181682505408369200000000000), (161371813152834900471798552495073908566237/378549881904677523903407734982000000000000, 234801619442934427368030242995218226743/113746959706934352134437420367187500000), (3048975254614759891814701372597570293465997778177/2469750881635821854892181682505408369200000000000, 7613536337479239425904849470322650093252685242911/2469750881635821854892181682505408369200000000000)]
def terminal19Triangle0 : Polygon :=
  [ { a := -26993294388582800452113443676977918546553653539477287112466964343494709180275600000000000, b := -660121764060109205003331949913093994144432719438518718980567053920500475699200000000000, c := -12869609267506917476753617354171305173498461419273826031782107954250403730348326829806547 },
    { a := 952191067369403450681325043593260205576815154317637456821612589208163699600685200000000000, b := -755641044759316333023749367380943291381892514502542477628524472353962286737113600000000000, c := -1153919438386311169045825072933536669267556856062457831222238902788169893257325920929840701 },
    { a := -130314414650303541700970923378961773241692424800000000000, b := 202579145155153329760120752279807199229673473200000000000, c := 463616903947601383463259992164726477396542698768146061893 } ]
private theorem terminal19_leaf0 :
    Polygon.carrier (terminal19Cut :: terminal19Domain) ⊆ terminal19Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal19Triangle0, l.contains p
  intro l hl
  simp only [terminal19Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal19Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 56298751 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs2 : ({ a := 123021907993758149169612758617956963300000000, b := 3426551628602214780095587922430054400000000, c := 78214798288046151217638325416097716857454339 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs3 : ({ a := 6250000, b := 6250000, c := 20030933 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs4 : ({ a := -50000000, b := 0, c := -25226609 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs5 : ({ a := 0, b := -50000000, c := -123209319 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs6 : ({ a := 10000000, b := -10000000, c := -19277981 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  simp only [Halfplane.contains, terminal19Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal19Triangle1Vertices : List QPoint :=
  [(757168368057743570999732798242216618859585182177/2469750881635821854892181682505408369200000000000, 9253015382317448660369147871266531421635576822911/2469750881635821854892181682505408369200000000000), (824690395464793375967160753946614707101136581089/2469750881635821854892181682505408369200000000000, 6828803071058439446529023034249923676807935962177/2469750881635821854892181682505408369200000000000), (2030082419510403372915701159788089002617217129089/2469750881635821854892181682505408369200000000000, 4973381604859490291764412217114350218204879302177/2469750881635821854892181682505408369200000000000)]
def terminal19Triangle1 : Polygon :=
  [ { a := -4976479723065798517318527192071786494364141404800000000, b := -138610796872392831204281030302470576024692326400000000, c := -2044983930871798330214034570532855379716023720577205347 },
    { a := -13253010472849636819747220122396953275736119000000000000, b := -8609943028897214263918145756010530682257718200000000000, c := -28231687804537963013814549402023594995008628616719595347 },
    { a := 8455703435964188246372337586939965569498847667929155808966422652773193819008523301594240000000, b := 2515024480657465959110560397993070862292839706719487527322517054437715357061291916728320000000, c := 12014957297297699452632102532794219808941157645431608898599054600762877497464037902388417601647 } ]
private theorem terminal19_leaf1 :
    Polygon.carrier ((⟨-terminal19Cut.a, -terminal19Cut.b, -terminal19Cut.c⟩ : Halfplane) :: terminal19Domain) ⊆ terminal19Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal19Triangle1, l.contains p
  intro l hl
  simp only [terminal19Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal19Cut.a, -terminal19Cut.b, -terminal19Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 56298751 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs2 : ({ a := 123021907993758149169612758617956963300000000, b := 3426551628602214780095587922430054400000000, c := 78214798288046151217638325416097716857454339 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs3 : ({ a := 6250000, b := 6250000, c := 20030933 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs4 : ({ a := -50000000, b := 0, c := -25226609 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs5 : ({ a := 0, b := -50000000, c := -123209319 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  have hs6 : ({ a := 10000000, b := -10000000, c := -19277981 } : Halfplane).contains p :=
    hp _ (by simp [terminal19Domain])
  simp only [Halfplane.contains, terminal19Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal19_cover_cert :
    PolygonCoverCert [terminal19Triangle0, terminal19Triangle1] terminal19Domain := by
  refine PolygonCoverCert.split terminal19Domain terminal19Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal19Triangle0 (by simp) terminal19_leaf0
  · exact PolygonCoverCert.leaf _ terminal19Triangle1 (by simp) terminal19_leaf1
theorem terminal19_polygon_cover :
    terminal19Domain.carrier ⊆ ⋃ K ∈ [terminal19Triangle0, terminal19Triangle1], Polygon.carrier K :=
  terminal19_cover_cert.sound

end
end ElevenSquare.Tasks.T07
