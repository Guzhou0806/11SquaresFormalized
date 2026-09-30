import ElevenSquare.Tasks.T05.TransportGeometry

namespace ElevenSquare.Pending.T05Transport
noncomputable section

def transportedSquare (q : UnitSquare) (g : Fin 4) (flip : Bool) : UnitSquare where
  center := physicalMap g flip q.center
  axis := mapAxis g flip q.axis
  axis_unit := by rw [mapAxis_normSq]; exact q.axis_unit

theorem transportedSquare_localX (q : UnitSquare) (g : Fin 4) (flip : Bool) (p : Point) :
    localX (transportedSquare q g flip) (physicalMap g flip p) = localX q p := by
  change dot (physicalMap g flip p - physicalMap g flip q.center) (mapAxis g flip q.axis) =
    dot (p-q.center) q.axis
  rw [physicalMap_eq_mapPoint g flip p, physicalMap_eq_mapPoint g flip q.center,
    mapPoint_sub, mapAxis_dot]

theorem transportedSquare_abs_localY (q : UnitSquare) (g : Fin 4) (flip : Bool) (p : Point) :
    |localY (transportedSquare q g flip) (physicalMap g flip p)| = |localY q p| := by
  change |dot (physicalMap g flip p - physicalMap g flip q.center) (perp (mapAxis g flip q.axis))| =
    |dot (p-q.center) (perp q.axis)|
  rw [physicalMap_eq_mapPoint g flip p, physicalMap_eq_mapPoint g flip q.center,
    mapPoint_sub, mapAxis_abs_perp_dot]

theorem transportedSquare_closed (q : UnitSquare) (g : Fin 4) (flip : Bool) (p : Point) :
    ClosedSquare (transportedSquare q g flip) (physicalMap g flip p) ↔ ClosedSquare q p := by
  unfold ClosedSquare
  rw [transportedSquare_localX, transportedSquare_abs_localY]

theorem transportedSquare_open (q : UnitSquare) (g : Fin 4) (flip : Bool) (p : Point) :
    OpenSquare (transportedSquare q g flip) (physicalMap g flip p) ↔ OpenSquare q p := by
  unfold OpenSquare
  rw [transportedSquare_localX, transportedSquare_abs_localY]

theorem physicalMap_surjective (g : Fin 4) (flip : Bool) :
    Function.Surjective (physicalMap g flip) := by
  intro p
  obtain ⟨q,hq⟩ := mapPoint_surjective coverCap g flip p
  exact ⟨q, (physicalMap_eq_mapPoint g flip q).trans hq⟩

theorem physicalMap_container (g : Fin 4) (flip : Bool) (p : Point)
    (hp : InContainer coverCap p) : InContainer coverCap (physicalMap g flip p) := by
  rw [physicalMap_eq_mapPoint]
  exact mapPoint_container coverCap g flip p hp

/-- Apply a physical symmetry to every complete square, without changing owner indices. -/
def transportedPacking (P : Packing 11 coverCap) (g : Fin 4) (flip : Bool) :
    Packing 11 coverCap where
  squares := fun i => transportedSquare (P.squares i) g flip
  side_nonneg := P.side_nonneg
  contained := by
    intro i p hp
    obtain ⟨q,rfl⟩ := physicalMap_surjective g flip p
    exact physicalMap_container g flip q
      (P.contained i q ((transportedSquare_closed (P.squares i) g flip q).mp hp))
  interior_disjoint := by
    intro i j hij p hp
    obtain ⟨q,rfl⟩ := physicalMap_surjective g flip p
    exact P.interior_disjoint i j hij q
      ⟨(transportedSquare_open (P.squares i) g flip q).mp hp.1,
       (transportedSquare_open (P.squares j) g flip q).mp hp.2⟩

theorem closed_square_iff (P : Packing 11 coverCap) (g : Fin 4) (flip : Bool)
    (i : Owner) (p : Point) :
    ClosedSquare ((transportedPacking P g flip).squares i) (physicalMap g flip p) ↔
      ClosedSquare (P.squares i) p :=
  transportedSquare_closed (P.squares i) g flip p

theorem open_square_iff (P : Packing 11 coverCap) (g : Fin 4) (flip : Bool)
    (i : Owner) (p : Point) :
    OpenSquare ((transportedPacking P g flip).squares i) (physicalMap g flip p) ↔
      OpenSquare (P.squares i) p :=
  transportedSquare_open (P.squares i) g flip p

theorem normalized_center (P : Packing 11 coverCap) (g : Fin 4) (flip : Bool) (i : Owner) :
    normalizeCenter ((transportedPacking P g flip).squares i).center =
      (if flip then halfTurn else id) (view g (normalizeCenter (P.squares i).center)) :=
  normalize_physicalMap g flip (P.squares i).center

/-- The same whole-square witness after an arbitrary owner reindexing. -/
theorem reindexed_closed_square_iff (P : Packing 11 coverCap) (g : Fin 4) (flip : Bool)
    (perm : Equiv.Perm Owner) (i : Owner) (p : Point) :
    ClosedSquare ((relabelPacking (transportedPacking P g flip) perm).squares i)
      (physicalMap g flip p) ↔ ClosedSquare (P.squares (perm i)) p :=
  closed_square_iff P g flip (perm i) p

end
end ElevenSquare.Pending.T05Transport
#print axioms ElevenSquare.Pending.T05Transport.closed_square_iff
#print axioms ElevenSquare.Pending.T05Transport.open_square_iff
#print axioms ElevenSquare.Pending.T05Transport.normalized_center
#print axioms ElevenSquare.Pending.T05Transport.reindexed_closed_square_iff
