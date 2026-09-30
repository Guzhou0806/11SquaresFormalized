import ElevenSquare.Tasks.T01.SelfHullGeometry

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

structure SelfHullCut where
  normal : QPoint
  extent : ℚ
  point : HullWitness

def SelfHullCut.halfplane (owned : List QPoint) (cut : SelfHullCut) : Halfplane :=
  ownedPointCut cut.normal (cut.point.eval owned) cut.extent

def SelfHullCut.Check (owned : List QPoint) (r : PoseRow) (cut : SelfHullCut) : Prop :=
  cut.point.Valid owned ∧ SupportExtentCheck cut.normal cut.extent r.lo r.hi

instance selfHullCutCheckDecidable (owned : List QPoint) (r : PoseRow) (cut : SelfHullCut) :
    Decidable (cut.Check owned r) := by
  unfold SelfHullCut.Check
  infer_instance

theorem self_hull_cut_necessary (owned : List QPoint) (r : PoseRow)
    (cut : SelfHullCut) (hc : cut.Check owned r) (q : UnitSquare)
    (hq : r.contains q) (hold : rationalHull owned ⊆ {p | OpenSquare q p}) :
    (cut.halfplane owned).contains q.center := by
  obtain ⟨t, _, _, hl, hu, ha⟩ := hq.2
  exact owned_point_cut_necessary cut.normal (cut.point.eval owned) cut.extent r.lo r.hi
    hc.2 q (hold (hullWitness_sound owned cut.point hc.1)) t hl hu ha

def applySelfCuts (owned : List QPoint) (r : PoseRow) (cuts : List SelfHullCut) : PoseRow :=
  {r with centers := cuts.map (SelfHullCut.halfplane owned) ++ r.centers}

theorem self_cut_row_keeps (owned : List QPoint) (r : PoseRow)
    (cuts : List SelfHullCut) (hc : ∀ c ∈ cuts, c.Check owned r) (q : UnitSquare)
    (hq : r.contains q) (hold : rationalHull owned ⊆ {p | OpenSquare q p}) :
    (applySelfCuts owned r cuts).contains q := by
  refine ⟨?_, hq.2⟩
  intro h hh
  rcases List.mem_append.mp hh with hh | hh
  · obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hh
    exact self_hull_cut_necessary owned r c (hc c hmem) q hq hold
  · exact hq.1 h hh

def selfCutOutput (owned : List QPoint) (plan : List (PoseRow × List SelfHullCut)) :
    List PoseRow := plan.map (fun item => applySelfCuts owned item.1 item.2)

/-- This is a state-preservation theorem using existing ownership. It is not
an `outerEquivalent` step: the restricted rows need not cover arbitrary squares
that fail to contain their previously proved owned hull. -/
theorem self_cut_rows_sound {S : ℝ} (P : Packing 11 S) (s : PoseState) (i : Owner)
    (plan : List (PoseRow × List SelfHullCut))
    (hinput : plan.map Prod.fst = s.rows i)
    (hchecks : ∀ item ∈ plan, ∀ c ∈ item.2, c.Check (s.owned i) item.1)
    (hs : StateHolds P s) :
    StateHolds P (replaceRows s i (selfCutOutput (s.owned i) plan)) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases hji : j = i
  · subst j
    obtain ⟨r, hr, hq⟩ := hs.1 i
    rw [← hinput] at hr
    obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
    simp only [replaceRows, Function.update_same]
    refine ⟨applySelfCuts (s.owned i) item.1 item.2, List.mem_map.mpr ⟨item, hm, rfl⟩, ?_⟩
    exact self_cut_row_keeps _ _ _ (hchecks item hm) _ hq (hs.2 i)
  · simpa only [replaceRows, Function.update_noteq hji] using hs.1 j

end
end ElevenSquare.Tasks.T01
