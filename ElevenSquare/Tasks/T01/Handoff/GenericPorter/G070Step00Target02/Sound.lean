import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge00
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge01
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge02
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge03
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge04
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge05
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge06
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge07
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge08
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge09
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge10
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Vertices

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem edge0_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v0 t) (v1 t)).contains p := by
  have hf : (symbolicFacetReal f0 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f0, by simp [facets], rfl⟩)
  rw [Edge00.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge1_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v1 t) (v2 t)).contains p := by
  have hf : (symbolicFacetReal f1 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f1, by simp [facets], rfl⟩)
  rw [Edge01.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge2_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v2 t) (v3 t)).contains p := by
  have hf : (symbolicFacetReal f2 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f2, by simp [facets], rfl⟩)
  rw [Edge02.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge3_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v3 t) (v4 t)).contains p := by
  have hf : (symbolicFacetReal f3 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f3, by simp [facets], rfl⟩)
  rw [Edge03.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge4_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v4 t) (v5 t)).contains p := by
  have hf : (symbolicFacetReal f4 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f4, by simp [facets], rfl⟩)
  rw [Edge04.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge5_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v5 t) (v6 t)).contains p := by
  have hf : (symbolicFacetReal f5 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f5, by simp [facets], rfl⟩)
  rw [Edge05.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge6_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v6 t) (v7 t)).contains p := by
  have hf : (symbolicFacetReal f6 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f6, by simp [facets], rfl⟩)
  rw [Edge06.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge7_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v7 t) (v8 t)).contains p := by
  have hf : (symbolicFacetReal f7 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f7, by simp [facets], rfl⟩)
  rw [Edge07.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge8_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v8 t) (v9 t)).contains p := by
  have hf : (symbolicFacetReal f8 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f8, by simp [facets], rfl⟩)
  rw [Edge08.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge9_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v9 t) (v10 t)).contains p := by
  have hf : (symbolicFacetReal f9 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f9, by simp [facets], rfl⟩)
  rw [Edge09.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem edge10_supported (t : ℝ) (p : Point)
    (hp : p ∈ RealPolygon.carrier (facets.map (fun f => symbolicFacetReal f t))) :
    (realEdge (v10 t) (v0 t)).contains p := by
  have hf : (symbolicFacetReal f10 t).contains p :=
    hp _ (List.mem_map.mpr ⟨f10, by simp [facets], rfl⟩)
  rw [Edge10.edge_scaled] at hf
  exact real_halfplane_scale_sound _ _ _ (by positivity) hf

theorem support_checked (t : ℝ) (hl : ((1/32 : ℚ) : ℝ) ≤ t)
    (hu : t ≤ ((5/128 : ℚ) : ℝ)) :
    RealPolygonSupportCheck (vertices t)
      (facets.map (fun f => symbolicFacetReal f t)) := by
  constructor
  · simp [vertices]
  · intro v hv
    simp only [vertices, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨v10 t, by simp [vertices], v1 t,
        by simp [vertices], ?_, ?_, Edge00.turn_positive t hl hu⟩
      · intro p hp; exact edge10_supported t p hp
      · intro p hp; exact edge0_supported t p hp
    · refine ⟨v0 t, by simp [vertices], v2 t,
        by simp [vertices], ?_, ?_, Edge01.turn_positive t hl hu⟩
      · intro p hp; exact edge0_supported t p hp
      · intro p hp; exact edge1_supported t p hp
    · refine ⟨v1 t, by simp [vertices], v3 t,
        by simp [vertices], ?_, ?_, Edge02.turn_positive t hl hu⟩
      · intro p hp; exact edge1_supported t p hp
      · intro p hp; exact edge2_supported t p hp
    · refine ⟨v2 t, by simp [vertices], v4 t,
        by simp [vertices], ?_, ?_, Edge03.turn_positive t hl hu⟩
      · intro p hp; exact edge2_supported t p hp
      · intro p hp; exact edge3_supported t p hp
    · refine ⟨v3 t, by simp [vertices], v5 t,
        by simp [vertices], ?_, ?_, Edge04.turn_positive t hl hu⟩
      · intro p hp; exact edge3_supported t p hp
      · intro p hp; exact edge4_supported t p hp
    · refine ⟨v4 t, by simp [vertices], v6 t,
        by simp [vertices], ?_, ?_, Edge05.turn_positive t hl hu⟩
      · intro p hp; exact edge4_supported t p hp
      · intro p hp; exact edge5_supported t p hp
    · refine ⟨v5 t, by simp [vertices], v7 t,
        by simp [vertices], ?_, ?_, Edge06.turn_positive t hl hu⟩
      · intro p hp; exact edge5_supported t p hp
      · intro p hp; exact edge6_supported t p hp
    · refine ⟨v6 t, by simp [vertices], v8 t,
        by simp [vertices], ?_, ?_, Edge07.turn_positive t hl hu⟩
      · intro p hp; exact edge6_supported t p hp
      · intro p hp; exact edge7_supported t p hp
    · refine ⟨v7 t, by simp [vertices], v9 t,
        by simp [vertices], ?_, ?_, Edge08.turn_positive t hl hu⟩
      · intro p hp; exact edge7_supported t p hp
      · intro p hp; exact edge8_supported t p hp
    · refine ⟨v8 t, by simp [vertices], v10 t,
        by simp [vertices], ?_, ?_, Edge09.turn_positive t hl hu⟩
      · intro p hp; exact edge8_supported t p hp
      · intro p hp; exact edge9_supported t p hp
    · refine ⟨v9 t, by simp [vertices], v0 t,
        by simp [vertices], ?_, ?_, Edge10.turn_positive t hl hu⟩
      · intro p hp; exact edge9_supported t p hp
      · intro p hp; exact edge10_supported t p hp

theorem target_sound (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hl : ((1/32 : ℚ) : ℝ) ≤ t) (hu : t ≤ ((5/128 : ℚ) : ℝ))
    (hc : SymbolicPolygonContains facets t q.center) :
    ∃ Q : Set Point,
      CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull owned) Q := by
  exact moving_symbolic_forbidden_support_sound owned locals q t facets
    (vertices t) witnesses locals_strict (support_checked t hl hu)
    (vertices_checked q t ha) hc

#print axioms target_sound

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02
