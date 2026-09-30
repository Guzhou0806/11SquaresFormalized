import ElevenSquare.Tasks.T07.LocalTraceCover
import Mathlib.Tactic.Linarith

/-! Generated exact polygon union certificates from far15y-self-300.json.
The emitter is untrusted; each closed split and arithmetic leaf is checked
inside Lean.  Triangle-to-semantic forbidden-center bridges are separate. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal step 7, row 30; interval ['7/128', '15/256']. -/
def terminal30Domain : Polygon :=
  [ { a := 12500000, b := 0, c := 7186857 },
    { a := 50000000, b := 50000000, c := 154735183 },
    { a := -1562500, b := 0, c := -849097 },
    { a := -3125000, b := -3125000, c := -9508839 },
    { a := 0, b := -100000000, c := -249940639 },
    { a := 6250000, b := -6250000, c := -12049477 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal30Triangle0Vertices : List QPoint :=
  [(1263994635240329534653298008557458101179477/3364090315217896815330105196502000000000000, 8444341059858952858623399910472739161898539/3364090315217896815330105196502000000000000), (10941681239651566496008981848897627653/25490273770963994090142326000000000000, 805466129682217345341443315713836523/398285527671312407658473843750000000), (7303970185976608998776724268701667200038539/3364090315217896815330105196502000000000000, 10592203897267357057992759085897128089100523/3364090315217896815330105196502000000000000)]
def terminal30Triangle0 : Polygon :=
  [ { a := -41830273840797606991745232915273756301277972398997098660776837138770000000000000, b := -4589234593207413378606984902766942887401796610888051204475793826304000000000000, c := -27236576681566816304235144105398202251075656827520885203219463938430960705836823 },
    { a := 7429221968370565724168145302847932192222228632910952542423411285658000000000000, b := -11490107366537644305280150588534894490690872253803179616205538540916000000000000, c := -20047839964579242908188624534113210133853041536738891078398750029734003999005453 },
    { a := -144512091394840894774819302461576514447369986776496475426764878027285199360000000000, b := 406380465087696006031362835251865617701285670246127017182475540110268022480000000000, c := 965774528798205230739770456710012022308092874090486184481321349044647524620937804561 } ]
private theorem terminal30_leaf0 :
    Polygon.carrier (terminal30Domain) ⊆ terminal30Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal30Triangle0, l.contains p
  intro l hl
  simp only [terminal30Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 12500000, b := 0, c := 7186857 } : Halfplane).contains p :=
    hp _ (by simp [terminal30Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 154735183 } : Halfplane).contains p :=
    hp _ (by simp [terminal30Domain])
  have hs2 : ({ a := -1562500, b := 0, c := -849097 } : Halfplane).contains p :=
    hp _ (by simp [terminal30Domain])
  have hs3 : ({ a := -3125000, b := -3125000, c := -9508839 } : Halfplane).contains p :=
    hp _ (by simp [terminal30Domain])
  have hs4 : ({ a := 0, b := -100000000, c := -249940639 } : Halfplane).contains p :=
    hp _ (by simp [terminal30Domain])
  have hs5 : ({ a := 6250000, b := -6250000, c := -12049477 } : Halfplane).contains p :=
    hp _ (by simp [terminal30Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal30_cover_cert :
    PolygonCoverCert [terminal30Triangle0] terminal30Domain :=
  PolygonCoverCert.leaf _ terminal30Triangle0 (by simp) terminal30_leaf0
theorem terminal30_polygon_cover :
    terminal30Domain.carrier ⊆ ⋃ K ∈ [terminal30Triangle0], Polygon.carrier K :=
  terminal30_cover_cert.sound

/-- Archived far15 terminal step 7, row 31; interval ['15/256', '1/16']. -/
def terminal31Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28740577 },
    { a := 20000000, b := 20000000, c := 61921117 },
    { a := -100000000, b := 100000000, c := 200245433 },
    { a := -4000000, b := 0, c := -2187203 },
    { a := 0, b := -100000000, c := -250294397 },
    { a := 6250000, b := -6250000, c := -12071413 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal31Triangle0Vertices : List QPoint :=
  [(5015398662031339032055243066241623540177757/13468417512116876978710527659974000000000000, 33750520724803403095391628900562108996201251/13468417512116876978710527659974000000000000), (1369762156726874402199062153757720211/3187738127716757816584282000000000000, 402157893250955522418227456623977161/199233632982297363536517625000000000), (29184950359873957576260297257274248765381251/13468417512116876978710527659974000000000000, 42451885798201106875456195006385016016182243/13468417512116876978710527659974000000000000)]
def terminal31Triangle0 : Polygon :=
  [ { a := -20924935151195248675445945845940281158660923032528483552121477675758000000000000, b := -2460751078438304566389548031370309148786465173855135246057983319040000000000000, c := -13958471502882831332377247531275077771737211445491031275356302380126761134857929 },
    { a := 48662608358848033880721054591812858477251218578065531499003483643502000000000000, b := -74585450398595909315256739304069926728868082697568891600783468562268000000000000, c := -129642343773703113632937331238635000586655576034356984300294566286755697725321303 },
    { a := -2343872354677435763848924620089615448686072532828125034859108958154384284160000000000, b := 6510512266944754407998780947419099671019610518425871091794301907195774983120000000000, c := 15441882814805590164470528018088531709767312694003030662263541588332532485286540223521 } ]
private theorem terminal31_leaf0 :
    Polygon.carrier (terminal31Domain) ⊆ terminal31Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal31Triangle0, l.contains p
  intro l hl
  simp only [terminal31Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 28740577 } : Halfplane).contains p :=
    hp _ (by simp [terminal31Domain])
  have hs1 : ({ a := 20000000, b := 20000000, c := 61921117 } : Halfplane).contains p :=
    hp _ (by simp [terminal31Domain])
  have hs2 : ({ a := -100000000, b := 100000000, c := 200245433 } : Halfplane).contains p :=
    hp _ (by simp [terminal31Domain])
  have hs3 : ({ a := -4000000, b := 0, c := -2187203 } : Halfplane).contains p :=
    hp _ (by simp [terminal31Domain])
  have hs4 : ({ a := 0, b := -100000000, c := -250294397 } : Halfplane).contains p :=
    hp _ (by simp [terminal31Domain])
  have hs5 : ({ a := 6250000, b := -6250000, c := -12071413 } : Halfplane).contains p :=
    hp _ (by simp [terminal31Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs2 ⊢
    linarith only [hs0, hs2]
theorem terminal31_cover_cert :
    PolygonCoverCert [terminal31Triangle0] terminal31Domain :=
  PolygonCoverCert.leaf _ terminal31Triangle0 (by simp) terminal31_leaf0
theorem terminal31_polygon_cover :
    terminal31Domain.carrier ⊆ ⋃ K ∈ [terminal31Triangle0], Polygon.carrier K :=
  terminal31_cover_cert.sound

/-- Archived far15 terminal step 7, row 32; interval ['1/16', '17/256']. -/
def terminal32Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28735927 },
    { a := 10000000, b := 10000000, c := 30974979 },
    { a := 0, b := 50000000, c := 127367657 },
    { a := -4000000, b := 0, c := -2200579 },
    { a := 0, b := -50000000, c := -125326521 },
    { a := 25000000, b := -25000000, c := -48372387 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal32Triangle0Vertices : List QPoint :=
  [(19435579232843982680433362763979282004349/52661316781956420440984183878000000000000, 131739502361281349074112993509837672094979/52661316781956420440984183878000000000000), (152438995401703507230762689397733861/354365440128085215806134000000000000, 44621701092540920258828049074590847/22147840008005325987883375000000000), (113888188570217199562506062283122530554979/52661316781956420440984183878000000000000, 166160813327060657610443697582396980915651/52661316781956420440984183878000000000000)]
def terminal32Triangle0 : Polygon :=
  [ { a := -9086526151165293938710315533045211952074922988706482615078566530000000000000, b := -1140340637781275778263015502491465800872194111879342916402016192000000000000, c := -6206259681260316499884418162862723374410349078595360947467305520002962886271 },
    { a := 7094749720446454864821596979247424666089929277254059345467389526000000000000, b := -10776799947101025172266006856584484025451273758630520848720516076000000000000, c := -18660255958303853381792544196202025284775974554807138418606006279246677092299 },
    { a := -906335780409567231389996512533585172178923567794898404637904287763008000000000000, b := 2486999390598892941463202442564435683976282849707266022236638456371570000000000000, c := 5887070817128149261590824811878406439759060417488245651827527296140229092942592121 } ]
private theorem terminal32_leaf0 :
    Polygon.carrier (terminal32Domain) ⊆ terminal32Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal32Triangle0, l.contains p
  intro l hl
  simp only [terminal32Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 28735927 } : Halfplane).contains p :=
    hp _ (by simp [terminal32Domain])
  have hs1 : ({ a := 10000000, b := 10000000, c := 30974979 } : Halfplane).contains p :=
    hp _ (by simp [terminal32Domain])
  have hs2 : ({ a := 0, b := 50000000, c := 127367657 } : Halfplane).contains p :=
    hp _ (by simp [terminal32Domain])
  have hs3 : ({ a := -4000000, b := 0, c := -2200579 } : Halfplane).contains p :=
    hp _ (by simp [terminal32Domain])
  have hs4 : ({ a := 0, b := -50000000, c := -125326521 } : Halfplane).contains p :=
    hp _ (by simp [terminal32Domain])
  have hs5 : ({ a := 25000000, b := -25000000, c := -48372387 } : Halfplane).contains p :=
    hp _ (by simp [terminal32Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs3 hs4 ⊢
    linarith only [hs3, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal32_cover_cert :
    PolygonCoverCert [terminal32Triangle0] terminal32Domain :=
  PolygonCoverCert.leaf _ terminal32Triangle0 (by simp) terminal32_leaf0
theorem terminal32_polygon_cover :
    terminal32Domain.carrier ⊆ ⋃ K ∈ [terminal32Triangle0], Polygon.carrier K :=
  terminal32_cover_cert.sound

/-- Archived far15 terminal step 7, row 33; interval ['17/256', '9/128']. -/
def terminal33Domain : Polygon :=
  [ { a := 3125000, b := 0, c := 1795837 },
    { a := 25000000, b := 25000000, c := 77475739 },
    { a := 0, b := 50000000, c := 127278787 },
    { a := -100000000, b := 0, c := -55345381 },
    { a := -20000000, b := -20000000, c := -61272407 },
    { a := 0, b := -100000000, c := -251016653 },
    { a := 25000000, b := -25000000, c := -48458213 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal33Triangle0Vertices : List QPoint :=
  [(197452174656564561424420754880460230772557/539800047419742593870547929717360000000000, 1348069481726165887623092514657095438604083/539800047419742593870547929717360000000000), (2198842496994907681015246213724571313/5105498754685642621248900400000000000, 22916875119248397280251235028510837/11396202577423309422430581250000000), (1165086210137658893435757201462105815259283/539800047419742593870547929717360000000000, 1704986800038737690621269277616330472057843/539800047419742593870547929717360000000000)]
def terminal33Triangle0 : Polygon :=
  [ { a := -1340569496497652981526642856580282248227476649108115002050594750749840000000000, b := -178843452327334005298366700025945968089475233702961225847140507770880000000000, c := -936998366095819689564621511521306601336846137773385703434459610673027304777347 },
    { a := 3162810420668227429966327675693702085090429665786672474276208996253840000000000, b := -4761410910812836033838882854104788617399526503965748747138685388319520000000000, c := -8212663128295104614049945370493511232303366031425873357974813106891889482284349 },
    { a := -96331992675026810467564731593062092063903583466950510236766664430714636800000000000, b := 261164449118825804000706681052873841202844123810551975813620561888925881680000000000, c := 616981906019095336570122033631952356044080150571449270320751809376661236032373218969 } ]
private theorem terminal33_leaf0 :
    Polygon.carrier (terminal33Domain) ⊆ terminal33Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal33Triangle0, l.contains p
  intro l hl
  simp only [terminal33Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 3125000, b := 0, c := 1795837 } : Halfplane).contains p :=
    hp _ (by simp [terminal33Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 77475739 } : Halfplane).contains p :=
    hp _ (by simp [terminal33Domain])
  have hs2 : ({ a := 0, b := 50000000, c := 127278787 } : Halfplane).contains p :=
    hp _ (by simp [terminal33Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -55345381 } : Halfplane).contains p :=
    hp _ (by simp [terminal33Domain])
  have hs4 : ({ a := -20000000, b := -20000000, c := -61272407 } : Halfplane).contains p :=
    hp _ (by simp [terminal33Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -251016653 } : Halfplane).contains p :=
    hp _ (by simp [terminal33Domain])
  have hs6 : ({ a := 25000000, b := -25000000, c := -48458213 } : Halfplane).contains p :=
    hp _ (by simp [terminal33Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
theorem terminal33_cover_cert :
    PolygonCoverCert [terminal33Triangle0] terminal33Domain :=
  PolygonCoverCert.leaf _ terminal33Triangle0 (by simp) terminal33_leaf0
theorem terminal33_polygon_cover :
    terminal33Domain.carrier ⊆ ⋃ K ∈ [terminal33Triangle0], Polygon.carrier K :=
  terminal33_cover_cert.sound

/-- Archived far15 terminal step 7, row 34; interval ['9/128', '19/256']. -/
def terminal34Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28732887 },
    { a := 20000000, b := 20000000, c := 62013011 },
    { a := 0, b := 20000000, c := 50878457 },
    { a := -100000000, b := 0, c := -55672769 },
    { a := -10000000, b := -10000000, c := -30705807 },
    { a := 0, b := -1000000, c := -2513853 },
    { a := 25000000, b := -25000000, c := -48543227 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal34Triangle0Vertices : List QPoint :=
  [(14405246988926197547071407787673373897137/39733914785073891681361201745200000000000, 14151172824990628519952067722177138645241/5676273540724841668765885963600000000000), (11013911701970652870976449526019817407/25541451274352295237282818000000000000, 801015815025783065286119941213686469/399085176161754613082544031250000000), (12227010150537477004866883831247155497241/5676273540724841668765885963600000000000, 125630583807449191771561965361573038430863/39733914785073891681361201745200000000000)]
def terminal34Triangle0 : Polygon :=
  [ { a := -13327859827142507873037627190981395628180377552253212941805084844400000000000, b := -1883646350101661677392222545933713684129977083608125965645520179200000000000, c := -9527924695609147640766422549674332579916833093053468682333005488398075763741 },
    { a := 1171827810199613567038443151509096630428162119751629114027851567210800000000000, b := -1748443258920317164710405720602828492503510585525857840727556197269600000000000, c := -3004040611353192764093081815863791644204302625255604150674549908877856048916751 },
    { a := -527912222722526523607912327221879717572325658136787480156463247509977600000000000, b := 1414205999733945726639201960277869484833085077163231087377653275605730000000000000, c := 3334280282888028814419775914721106610653056864721975977765131731347325598281292369 } ]
private theorem terminal34_leaf0 :
    Polygon.carrier (terminal34Domain) ⊆ terminal34Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal34Triangle0, l.contains p
  intro l hl
  simp only [terminal34Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 28732887 } : Halfplane).contains p :=
    hp _ (by simp [terminal34Domain])
  have hs1 : ({ a := 20000000, b := 20000000, c := 62013011 } : Halfplane).contains p :=
    hp _ (by simp [terminal34Domain])
  have hs2 : ({ a := 0, b := 20000000, c := 50878457 } : Halfplane).contains p :=
    hp _ (by simp [terminal34Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -55672769 } : Halfplane).contains p :=
    hp _ (by simp [terminal34Domain])
  have hs4 : ({ a := -10000000, b := -10000000, c := -30705807 } : Halfplane).contains p :=
    hp _ (by simp [terminal34Domain])
  have hs5 : ({ a := 0, b := -1000000, c := -2513853 } : Halfplane).contains p :=
    hp _ (by simp [terminal34Domain])
  have hs6 : ({ a := 25000000, b := -25000000, c := -48543227 } : Halfplane).contains p :=
    hp _ (by simp [terminal34Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs3 hs4 ⊢
    linarith only [hs3, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs3 hs6 ⊢
    linarith only [hs3, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal34_cover_cert :
    PolygonCoverCert [terminal34Triangle0] terminal34Domain :=
  PolygonCoverCert.leaf _ terminal34Triangle0 (by simp) terminal34_leaf0
theorem terminal34_polygon_cover :
    terminal34Domain.carrier ⊆ ⋃ K ∈ [terminal34Triangle0], Polygon.carrier K :=
  terminal34_cover_cert.sound

/-- Archived far15 terminal step 7, row 35; interval ['19/256', '5/64']. -/
def terminal35Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 57468657 },
    { a := 100000000, b := 100000000, c := 310236057 },
    { a := -25000000, b := 25000000, c := 49560707 },
    { a := -50000000, b := 0, c := -27998307 },
    { a := -50000000, b := -50000000, c := -153877833 },
    { a := 0, b := -100000000, c := -251759051 },
    { a := 50000000, b := -50000000, c := -97255051 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal35Triangle0Vertices : List QPoint :=
  [(4859944283918614114162589897738354566956213/13524887941785606087364353751318000000000000, 33659472846146057068921195753898942457081291/13524887941785606087364353751318000000000000), (613039184439499773239753833823762251/1419788010666354551730922000000000000, 1388830168788201468907786508663293/693255864583180933462364257812500), (29074759941273931992797547459543799796341291/13524887941785606087364353751318000000000000, 42806361178318380693763948833191250737563787/13524887941785606087364353751318000000000000)]
def terminal35Triangle0 : Polygon :=
  [ { a := -19376611457170777277259678688725700800804215223234614347382447950000000000000, b := -2892298641691772375048793781097236624698679504372622989970639872000000000000, c := -14160745768121526464117036843159721714633515357646113758095641108325923905689 },
    { a := 7435597499940458960356957961277901656437533535421932579839026801754000000000000, b := -10996236434718419584676664095595989188800370410627831212188900067828000000000000, c := -18818688716058408807914100171680627649038175288877988983701687800804775386674029 },
    { a := -2474212794173138265635634351853707177888207192634304731624205270812718594560000000000, b := 6550053365934524666275912840764320609410085148045399426999508523513440656080000000000, c := 15412091248552019148300181806486399202459897583094322762908698796561734069642336868561 } ]
private theorem terminal35_leaf0 :
    Polygon.carrier (terminal35Domain) ⊆ terminal35Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal35Triangle0, l.contains p
  intro l hl
  simp only [terminal35Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 57468657 } : Halfplane).contains p :=
    hp _ (by simp [terminal35Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 310236057 } : Halfplane).contains p :=
    hp _ (by simp [terminal35Domain])
  have hs2 : ({ a := -25000000, b := 25000000, c := 49560707 } : Halfplane).contains p :=
    hp _ (by simp [terminal35Domain])
  have hs3 : ({ a := -50000000, b := 0, c := -27998307 } : Halfplane).contains p :=
    hp _ (by simp [terminal35Domain])
  have hs4 : ({ a := -50000000, b := -50000000, c := -153877833 } : Halfplane).contains p :=
    hp _ (by simp [terminal35Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -251759051 } : Halfplane).contains p :=
    hp _ (by simp [terminal35Domain])
  have hs6 : ({ a := 50000000, b := -50000000, c := -97255051 } : Halfplane).contains p :=
    hp _ (by simp [terminal35Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs2 ⊢
    linarith only [hs0, hs2]
theorem terminal35_cover_cert :
    PolygonCoverCert [terminal35Triangle0] terminal35Domain :=
  PolygonCoverCert.leaf _ terminal35Triangle0 (by simp) terminal35_leaf0
theorem terminal35_polygon_cover :
    terminal35Domain.carrier ⊆ ⋃ K ∈ [terminal35Triangle0], Polygon.carrier K :=
  terminal35_cover_cert.sound

/-- Archived far15 terminal step 7, row 36; interval ['5/64', '21/256']. -/
def terminal36Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 57475267 },
    { a := 100000000, b := 100000000, c := 310415933 },
    { a := -50000000, b := 50000000, c := 98891073 },
    { a := -100000000, b := 0, c := -56316893 },
    { a := -50000000, b := -50000000, c := -154227433 },
    { a := 0, b := -25000000, c := -63034493 },
    { a := 20000000, b := -20000000, c := -38968961 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal36Triangle0Vertices : List QPoint :=
  [(301423910336011279248493153691593865766597/846317082864069125130089846774000000000000, 2102548695616129672252930803370160055894971/846317082864069125130089846774000000000000), (5528296669397783773546794758523282949/12785846263177236593932918000000000000, 49933857235147302951443030582936887/24972355982768040222525230468750000), (1815661227999273296459233750902535101074971/846317082864069125130089846774000000000000, 2681285355969533702182165215100463842593403/846317082864069125130089846774000000000000)]
def terminal36Triangle0 : Polygon :=
  [ { a := -5245807670594476725782799762274644611529036040421744974183040655922000000000000, b := -824732132849921290778113145842093193282083164384133482799593716480000000000000, c := -3917268596160451214762366134048975035579918889561777888442489006653550292217511 },
    { a := 12645445636737721215647791073868257165568891722513401328384344440498000000000000, b := -18536073416758419528954430733586322123926756419460332904691605938852000000000000, c := -31596498992598246022036043869365827177189046043714716901095750890472399828116377 },
    { a := -391835777709429173735220886567900378190935142285798419948856798580846694400000000, b := 1025219927558947746655885214225445770177322626097781139528267721839268380800000000, c := 2407450103910105180696126431467527724710020451921697684571881033681676065451522329 } ]
private theorem terminal36_leaf0 :
    Polygon.carrier (terminal36Domain) ⊆ terminal36Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal36Triangle0, l.contains p
  intro l hl
  simp only [terminal36Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 57475267 } : Halfplane).contains p :=
    hp _ (by simp [terminal36Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 310415933 } : Halfplane).contains p :=
    hp _ (by simp [terminal36Domain])
  have hs2 : ({ a := -50000000, b := 50000000, c := 98891073 } : Halfplane).contains p :=
    hp _ (by simp [terminal36Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -56316893 } : Halfplane).contains p :=
    hp _ (by simp [terminal36Domain])
  have hs4 : ({ a := -50000000, b := -50000000, c := -154227433 } : Halfplane).contains p :=
    hp _ (by simp [terminal36Domain])
  have hs5 : ({ a := 0, b := -25000000, c := -63034493 } : Halfplane).contains p :=
    hp _ (by simp [terminal36Domain])
  have hs6 : ({ a := 20000000, b := -20000000, c := -38968961 } : Halfplane).contains p :=
    hp _ (by simp [terminal36Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs2 ⊢
    linarith only [hs0, hs2]
theorem terminal36_cover_cert :
    PolygonCoverCert [terminal36Triangle0] terminal36Domain :=
  PolygonCoverCert.leaf _ terminal36Triangle0 (by simp) terminal36_leaf0
theorem terminal36_polygon_cover :
    terminal36Domain.carrier ⊆ ⋃ K ∈ [terminal36Triangle0], Polygon.carrier K :=
  terminal36_cover_cert.sound

/-- Archived far15 terminal step 7, row 37; interval ['21/256', '11/128']. -/
def terminal37Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 57485443 },
    { a := 2000000, b := 2000000, c := 6212093 },
    { a := -50000000, b := 50000000, c := 98668741 },
    { a := -100000000, b := 0, c := -56633583 },
    { a := -10000000, b := -10000000, c := -30915571 },
    { a := 0, b := -50000000, c := -126261063 },
    { a := 100000000, b := -100000000, c := -195177383 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal37Triangle0Vertices : List QPoint :=
  [(4786296201581322246434686303554602188575149/13558088649233720252465196020518000000000000, 33623707811324051275968080524820793888324819/13558088649233720252465196020518000000000000), (11079575758624367757310511050676353547/25587976277432569007410538000000000000, 797942430646841468682730322224486741/399812129334883890740789656250000000), (29027740416762737913126962422163251871584819/13558088649233720252465196020518000000000000, 42997019846591458280859337984525248803944851/13558088649233720252465196020518000000000000)]
def terminal37Triangle0 : Polygon :=
  [ { a := -167973888287009983484438859868480144908137956864475241618041510624990000000000000, b := -27746236668501638663552217772899141089463937139252485325327326557184000000000000, c := -128108333188739876685251566799036895114126518990866286098135587009182802732420817 },
    { a := 407817974286405585560144850716002286839539118057774279161738551322206000000000000, b := -592543262840265406129404835934200094126559940250517820221533787345276000000000000, c := -1006009068852196403373575772669380345579094359879307791375302283397231291866395759 },
    { a := -63542097755542425723998501977102584010471632018100807391215423182481908288000000000000, b := 164333824827441790844212241147764631985450258603996480495193240320656204530000000000000, c := 385111894712567359343965347297561865371683078544565541190939405680960709449094258107481 } ]
private theorem terminal37_leaf0 :
    Polygon.carrier (terminal37Domain) ⊆ terminal37Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal37Triangle0, l.contains p
  intro l hl
  simp only [terminal37Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 57485443 } : Halfplane).contains p :=
    hp _ (by simp [terminal37Domain])
  have hs1 : ({ a := 2000000, b := 2000000, c := 6212093 } : Halfplane).contains p :=
    hp _ (by simp [terminal37Domain])
  have hs2 : ({ a := -50000000, b := 50000000, c := 98668741 } : Halfplane).contains p :=
    hp _ (by simp [terminal37Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -56633583 } : Halfplane).contains p :=
    hp _ (by simp [terminal37Domain])
  have hs4 : ({ a := -10000000, b := -10000000, c := -30915571 } : Halfplane).contains p :=
    hp _ (by simp [terminal37Domain])
  have hs5 : ({ a := 0, b := -50000000, c := -126261063 } : Halfplane).contains p :=
    hp _ (by simp [terminal37Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -195177383 } : Halfplane).contains p :=
    hp _ (by simp [terminal37Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs3 hs6 ⊢
    linarith only [hs3, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs2 ⊢
    linarith only [hs0, hs2]
theorem terminal37_cover_cert :
    PolygonCoverCert [terminal37Triangle0] terminal37Domain :=
  PolygonCoverCert.leaf _ terminal37Triangle0 (by simp) terminal37_leaf0
theorem terminal37_polygon_cover :
    terminal37Domain.carrier ⊆ ⋃ K ∈ [terminal37Triangle0], Polygon.carrier K :=
  terminal37_cover_cert.sound

/-- Archived far15 terminal step 7, row 38; interval ['11/128', '23/256']. -/
def terminal38Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 57499027 },
    { a := 50000000, b := 50000000, c := 155401087 },
    { a := -100000000, b := 0, c := -56946663 },
    { a := 0, b := -5000000, c := -12645579 },
    { a := 100000000, b := -100000000, c := -195508193 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal38Triangle0Vertices : List QPoint :=
  [(237524133928526294981477576873415411698169/678796772832077555180239870401200000000000, 1680412832263287365586556929819361057798791/678796772832077555180239870401200000000000), (82249278365906641103454323034941359/189666929223916069554005200000000000, 5903469050929317855331929834685529/2963545769123688586781331250000000), (1450311973935738901905544950328006805682791/678796772832077555180239870401200000000000, 2154786579466026112333306733209931652469831/678796772832077555180239870401200000000000)]
def terminal38Triangle0 : Polygon :=
  [ { a := -12450874869121935352400672121583568737128393051983269033903531337200000000000, b := -2156014324750176586810040188244488661787396338963091717362869350400000000000, c := -9694178981346121359514298549767356160028934133999016575583820352020315985461 },
    { a := 50742462093998460073336888482560876791841266899720570175375368698000000000000, b := -73081891263507718802876180807149732278183910419158314082277653760800000000000, c := -123576719118325634049899533890287519147450129766177694491283245262023522790589 },
    { a := -161001684358739419332581638223753499119057468516046508418413932473410624000000000000, b := 411618235963440957581643576826550229160179321515791407672049559272885173200000000000, c := 962654517849117279332558587746099526928486507393083461948291285690897872474749433121 } ]
private theorem terminal38_leaf0 :
    Polygon.carrier (terminal38Domain) ⊆ terminal38Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal38Triangle0, l.contains p
  intro l hl
  simp only [terminal38Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 57499027 } : Halfplane).contains p :=
    hp _ (by simp [terminal38Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 155401087 } : Halfplane).contains p :=
    hp _ (by simp [terminal38Domain])
  have hs2 : ({ a := -100000000, b := 0, c := -56946663 } : Halfplane).contains p :=
    hp _ (by simp [terminal38Domain])
  have hs3 : ({ a := 0, b := -5000000, c := -12645579 } : Halfplane).contains p :=
    hp _ (by simp [terminal38Domain])
  have hs4 : ({ a := 100000000, b := -100000000, c := -195508193 } : Halfplane).contains p :=
    hp _ (by simp [terminal38Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal38_cover_cert :
    PolygonCoverCert [terminal38Triangle0] terminal38Domain :=
  PolygonCoverCert.leaf _ terminal38Triangle0 (by simp) terminal38_leaf0
theorem terminal38_polygon_cover :
    terminal38Domain.carrier ⊆ ⋃ K ∈ [terminal38Triangle0], Polygon.carrier K :=
  terminal38_cover_cert.sound

/-- Archived far15 terminal step 7, row 39; interval ['23/256', '3/32']. -/
def terminal39Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28757931 },
    { a := 10000000, b := 10000000, c := 31100847 },
    { a := -10000000, b := 0, c := -5725611 },
    { a := -20000000, b := -20000000, c := -62112501 },
    { a := 0, b := -50000000, c := -126653197 },
    { a := 20000000, b := -20000000, c := -39167517 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal39Triangle0Vertices : List QPoint :=
  [(943067917488609661750225680313542419393289/2718923073423741149805488431111600000000000, 6718884700883276378464751736448130706018679/2718923073423741149805488431111600000000000), (2782205950278663480515264298542188913/6405717507435693583751582000000000000, 398009694724103086292164552850584607/200178672107365424492236937500000000), (5797214831547954760071543435244601825230679/2718923073423741149805488431111600000000000, 8639341807750848501479010389758694280230711/2718923073423741149805488431111600000000000)]
def terminal39Triangle0 : Polygon :=
  [ { a := -8410229601075330055947957333271226519342506487324954542781968307659600000000000, b := -1523577283471777041087667990972971719525068316778361258338339852492800000000000, c := -6682115427834140164539099394755477521000626226211350012449393219992599244628391 },
    { a := 20712135312816237574257878997489689818817950402339365158806051742283600000000000, b := -29570716587583114957227032049582504020118480632810107796488107398487200000000000, c := -49798698387326577621871732234724623088463441453394269119451285644882604423553753 },
    { a := -2610787569691422651685624472375156724483983852000089642066014305941927385600000000000, b := 6599026023212301636891777369993843309638469985380391780593583870963271362000000000000, c := 15401665976156650222813290137158400226131970004337134227094087329611951295407646377281 } ]
private theorem terminal39_leaf0 :
    Polygon.carrier (terminal39Domain) ⊆ terminal39Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal39Triangle0, l.contains p
  intro l hl
  simp only [terminal39Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 28757931 } : Halfplane).contains p :=
    hp _ (by simp [terminal39Domain])
  have hs1 : ({ a := 10000000, b := 10000000, c := 31100847 } : Halfplane).contains p :=
    hp _ (by simp [terminal39Domain])
  have hs2 : ({ a := -10000000, b := 0, c := -5725611 } : Halfplane).contains p :=
    hp _ (by simp [terminal39Domain])
  have hs3 : ({ a := -20000000, b := -20000000, c := -62112501 } : Halfplane).contains p :=
    hp _ (by simp [terminal39Domain])
  have hs4 : ({ a := 0, b := -50000000, c := -126653197 } : Halfplane).contains p :=
    hp _ (by simp [terminal39Domain])
  have hs5 : ({ a := 20000000, b := -20000000, c := -39167517 } : Halfplane).contains p :=
    hp _ (by simp [terminal39Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal39_cover_cert :
    PolygonCoverCert [terminal39Triangle0] terminal39Domain :=
  PolygonCoverCert.leaf _ terminal39Triangle0 (by simp) terminal39_leaf0
theorem terminal39_polygon_cover :
    terminal39Domain.carrier ⊆ ⋃ K ∈ [terminal39Triangle0], Polygon.carrier K :=
  terminal39_cover_cert.sound

end
end ElevenSquare.Tasks.T07
