import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell01Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell02Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell03Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell05Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell06Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell07Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell09Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell10Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell11Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell12Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell14Data
import ElevenSquare.Tasks.T01.Handoff.Groups.G070.Mask
import ElevenSquare.Tasks.T01.Handoff.Plan

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots
noncomputable section

def physicalCell : Owner → Fin 16 := ![1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 14]

theorem physicalCell_injective : Function.Injective physicalCell := by decide
theorem physicalCell_image : Finset.univ.image physicalCell = mask := by decide

def owned00 : List QPoint := [((1543883109/1000000000 : ℚ), (629214151/1000000000 : ℚ)),
  ((783959637/500000000 : ℚ), (305477393/500000000 : ℚ)),
  ((1603637329/1000000000 : ℚ), (63990253/100000000 : ℚ)),
  ((1572048057/1000000000 : ℚ), (232270007/250000000 : ℚ)),
  ((1543883109/1000000000 : ℚ), (339364257/500000000 : ℚ))]

def owned01 : List QPoint := [((559224399/250000000 : ℚ), (1943513/1953125 : ℚ)),
  ((561353533/250000000 : ℚ), (6081077/6250000 : ℚ)),
  ((2265303257/1000000000 : ℚ), (930682669/1000000000 : ℚ)),
  ((580724397/250000000 : ℚ), (442208669/500000000 : ℚ)),
  ((292877443/125000000 : ℚ), (224655049/250000000 : ℚ)),
  ((294604953/125000000 : ℚ), (249496063/250000000 : ℚ)),
  ((1119317069/500000000 : ℚ), (249496063/250000000 : ℚ))]

def owned02 : List QPoint := [((1439673887/500000000 : ℚ), (359788647/500000000 : ℚ)),
  ((1451239527/500000000 : ℚ), (706762123/1000000000 : ℚ)),
  ((3058261939/1000000000 : ℚ), (40587311/50000000 : ℚ)),
  ((1537998631/500000000 : ℚ), (830458721/1000000000 : ℚ)),
  ((3033327231/1000000000 : ℚ), (486019933/500000000 : ℚ)),
  ((1511413727/500000000 : ℚ), (497957757/500000000 : ℚ)),
  ((1439673887/500000000 : ℚ), (497957757/500000000 : ℚ))]

def owned03 : List QPoint := [((388577001/250000000 : ℚ), (697416393/500000000 : ℚ)),
  ((1568029557/1000000000 : ℚ), (692537447/500000000 : ℚ)),
  ((1581869453/1000000000 : ℚ), (697977707/500000000 : ℚ)),
  ((1578676189/1000000000 : ℚ), (703786829/500000000 : ℚ)),
  ((780863371/500000000 : ℚ), (177525529/125000000 : ℚ)),
  ((779757357/500000000 : ℚ), (1418567763/1000000000 : ℚ))]

def owned04 : List QPoint := [((46140627/20000000 : ℚ), (848529289/500000000 : ℚ)),
  ((2328225149/1000000000 : ℚ), (840840183/500000000 : ℚ)),
  ((2338878059/1000000000 : ℚ), (844991681/500000000 : ℚ)),
  ((1170686087/500000000 : ℚ), (1702055787/1000000000 : ℚ)),
  ((2327777477/1000000000 : ℚ), (427931687/250000000 : ℚ))]

def owned05 : List QPoint := [((180050283/62500000 : ℚ), (1448584901/1000000000 : ℚ)),
  ((2944795153/1000000000 : ℚ), (1418113041/1000000000 : ℚ)),
  ((2993103927/1000000000 : ℚ), (1399934221/1000000000 : ℚ)),
  ((3080549913/1000000000 : ℚ), (1452336041/1000000000 : ℚ)),
  ((1533873877/500000000 : ℚ), (1486952043/1000000000 : ℚ)),
  ((3047858629/1000000000 : ℚ), (305848339/200000000 : ℚ)),
  ((3018841763/1000000000 : ℚ), (1554336589/1000000000 : ℚ)),
  ((1486197139/500000000 : ℚ), (1541873753/1000000000 : ℚ)),
  ((728792327/250000000 : ℚ), (1520103527/1000000000 : ℚ)),
  ((180050283/62500000 : ℚ), (1504634021/1000000000 : ℚ))]

def owned06 : List QPoint := [((191963927/125000000 : ℚ), (2175027803/1000000000 : ℚ)),
  ((1549306113/1000000000 : ℚ), (1082678421/500000000 : ℚ)),
  ((19625653/12500000 : ℚ), (545006253/250000000 : ℚ)),
  ((1548858441/1000000000 : ℚ), (274425403/125000000 : ℚ)),
  ((1538205531/1000000000 : ℚ), (546775057/250000000 : ℚ))]

def owned07 : List QPoint := [((2295214137/1000000000 : ℚ), (155070511/62500000 : ℚ)),
  ((2298407401/1000000000 : ℚ), (617377483/250000000 : ℚ)),
  ((144709803/62500000 : ℚ), (1228439679/500000000 : ℚ)),
  ((579392219/250000000 : ℚ), (2458515827/1000000000 : ℚ)),
  ((1161387793/500000000 : ℚ), (620562701/250000000 : ℚ)),
  ((2309054033/1000000000 : ℚ), (311501087/125000000 : ℚ))]

def owned08 : List QPoint := [((288115159/100000000 : ℚ), (554210361/250000000 : ℚ)),
  ((734588649/250000000 : ℚ), (2189911489/1000000000 : ℚ)),
  ((752258247/250000000 : ℚ), (2164513839/1000000000 : ℚ)),
  ((3094392239/1000000000 : ℚ), (277553367/125000000 : ℚ)),
  ((3086707999/1000000000 : ℚ), (2246760407/1000000000 : ℚ)),
  ((3019092373/1000000000 : ℚ), (2290732051/1000000000 : ℚ)),
  ((733755081/250000000 : ℚ), (565346659/250000000 : ℚ)),
  ((288115159/100000000 : ℚ), (447239513/200000000 : ℚ))]

def owned09 : List QPoint := [((100135791/125000000 : ℚ), (3046624869/1000000000 : ℚ)),
  ((843756359/1000000000 : ℚ), (726260931/250000000 : ℚ)),
  ((106782017/125000000 : ℚ), (720292019/250000000 : ℚ)),
  ((124716977/125000000 : ℚ), (720292019/250000000 : ℚ)),
  ((124716977/125000000 : ℚ), (394688287/125000000 : ℚ)),
  ((121825567/125000000 : ℚ), (3170321467/1000000000 : ℚ)),
  ((818821651/1000000000 : ℚ), (306533737/100000000 : ℚ))]

def owned10 : List QPoint := [((2273446261/1000000000 : ℚ), (161859053/50000000 : ℚ)),
  ((2305035533/1000000000 : ℚ), (1474001781/500000000 : ℚ)),
  ((2333200481/1000000000 : ℚ), (799588769/250000000 : ℚ)),
  ((2333200481/1000000000 : ℚ), (3247869439/1000000000 : ℚ)),
  ((577291079/250000000 : ℚ), (816532201/250000000 : ℚ))]

def ownedAt : Owner → List QPoint := ![owned00, owned01, owned02, owned03, owned04, owned05, owned06, owned07, owned08, owned09, owned10]

def cellRoots : Owner → CellRootCertificate 32 := ![Cell01Data.root owned00,
  Cell02Data.root owned01,
  Cell03Data.root owned02,
  Cell05Data.root owned03,
  Cell06Data.root owned04,
  Cell07Data.root owned05,
  Cell09Data.root owned06,
  Cell10Data.root owned07,
  Cell11Data.root owned08,
  Cell12Data.root owned09,
  Cell14Data.root owned10]

def root : PoseState where
  rows := fun i => (cellRoots i).rows
  owned := ownedAt

/-- The concrete wall-domain and strict ownership checks are separate required
premises. This lemma only selects the actual owner permutation and assembles them. -/
theorem initialized_of_checks
    (hdomains : ∀ i : Owner, (cellRoots i).DomainCheck (physicalCell i))
    (howned : ∀ (i : Owner) (q : UnitSquare),
      ClosedCell (physicalCell i) (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      rationalHull (ownedAt i) ⊆ {p | OpenSquare q p}) :
    RootValid mask root := by
  intro P hc ho
  have ho' : Occupies P (Finset.univ.image physicalCell) := by
    rwa [physicalCell_image]
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P physicalCell
    physicalCell_injective ho'
  refine ⟨perm, ?_, ?_⟩
  · intro i
    exact wall_seed_pose_cover (by decide : 0 < 32) (physicalCell i)
      (cellRoots i) (hdomains i) ((relabelPacking P perm).squares i)
      (hcell i) ((relabelPacking P perm).contained i) (hc (perm i))
  · intro i
    exact howned i ((relabelPacking P perm).squares i) (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G070

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.physicalCell_injective
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.initialized_of_checks
