import ElevenSquare.Tasks.T01.Quadratic

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Negating a core vertex permutes its four strict quadratic checks. -/
theorem baseline_core_vertex_check_neg (v : QPoint) (l u : ℚ)
    (h : BaselineCoreVertexCheck v l u) :
    BaselineCoreVertexCheck (-v.1, -v.2) l u := by
  rcases h with ⟨h1, h2, h3, h4⟩
  simp only [BaselineCoreVertexCheck, Prod.fst, Prod.snd,
    sub_neg_eq_add, sub_eq_add_neg, mul_neg, neg_mul, neg_neg]
  simp only [sub_eq_add_neg, neg_mul] at h1 h2 h3 h4
  exact ⟨h2, h1, h4, h3⟩

/-- A quarter turn permutes the checks in the order 4, 3, 1, 2. -/
theorem baseline_core_vertex_check_quarter_turn (v : QPoint) (l u : ℚ)
    (h : BaselineCoreVertexCheck v l u) :
    BaselineCoreVertexCheck (-v.2, v.1) l u := by
  rcases h with ⟨h1, h2, h3, h4⟩
  simp only [BaselineCoreVertexCheck, Prod.fst, Prod.snd,
    sub_neg_eq_add, sub_eq_add_neg, mul_neg, neg_mul, neg_neg]
  simp only [sub_eq_add_neg, neg_mul] at h1 h2 h3 h4
  exact ⟨h4, h3, h1, h2⟩

/-- The standard four-vertex square orbit from one rational vertex. -/
def coreQuarterTurnOrbit (v : QPoint) : List QPoint :=
  [v, (-v.2, v.1), (-v.1, -v.2), (v.2, -v.1)]

theorem baseline_core_quarter_turn_orbit_checked (v : QPoint) (l u : ℚ)
    (h : BaselineCoreVertexCheck v l u) :
    ∀ w ∈ coreQuarterTurnOrbit v, BaselineCoreVertexCheck w l u := by
  intro w hw
  simp only [coreQuarterTurnOrbit, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact h
  · exact baseline_core_vertex_check_quarter_turn v l u h
  · exact baseline_core_vertex_check_neg v l u h
  · simpa only [neg_neg] using
      baseline_core_vertex_check_quarter_turn (-v.1, -v.2) l u
        (baseline_core_vertex_check_neg v l u h)

/-- A concrete core list may use any ordering or a subset of this orbit. -/
theorem baseline_core_vertices_of_orbit (Q : List QPoint) (v : QPoint) (l u : ℚ)
    (hQ : ∀ w ∈ Q, w ∈ coreQuarterTurnOrbit v)
    (h : BaselineCoreVertexCheck v l u) :
    ∀ w ∈ Q, BaselineCoreVertexCheck w l u := by
  intro w hw
  exact baseline_core_quarter_turn_orbit_checked v l u h w (hQ w hw)

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.baseline_core_vertices_of_orbit
