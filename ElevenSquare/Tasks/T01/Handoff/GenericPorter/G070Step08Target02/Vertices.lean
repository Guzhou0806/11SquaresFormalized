import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Data

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.GenericPorter
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def w0 : MovingDifferenceWitness := ⟨.vertex 0, 1⟩
def w1 : MovingDifferenceWitness := ⟨.vertex 1, 1⟩
def w2 : MovingDifferenceWitness := ⟨.vertex 1, 2⟩
def w3 : MovingDifferenceWitness := ⟨.vertex 2, 2⟩
def w4 : MovingDifferenceWitness := ⟨.vertex 3, 2⟩
def w5 : MovingDifferenceWitness := ⟨.vertex 3, 3⟩
def w6 : MovingDifferenceWitness := ⟨.vertex 4, 3⟩
def w7 : MovingDifferenceWitness := ⟨.vertex 4, 0⟩
def w8 : MovingDifferenceWitness := ⟨.vertex 5, 0⟩
def w9 : MovingDifferenceWitness := ⟨.vertex 6, 0⟩
def w10 : MovingDifferenceWitness := ⟨.vertex 7, 0⟩
def w11 : MovingDifferenceWitness := ⟨.vertex 7, 1⟩
def witnesses : List MovingDifferenceWitness := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11]

theorem vertex0_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v0 t = w0.eval owned locals q := by
  change realPoint k0 - chartLocalOffset ab1.1 ab1.2 t =
    realPoint k0 - localOffset q ab1.1 ab1.2
  rw [chartLocalOffset_eq q ab1.1 ab1.2 t ha]

theorem vertex1_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v1 t = w1.eval owned locals q := by
  change realPoint k1 - chartLocalOffset ab1.1 ab1.2 t =
    realPoint k1 - localOffset q ab1.1 ab1.2
  rw [chartLocalOffset_eq q ab1.1 ab1.2 t ha]

theorem vertex2_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v2 t = w2.eval owned locals q := by
  change realPoint k1 - chartLocalOffset ab2.1 ab2.2 t =
    realPoint k1 - localOffset q ab2.1 ab2.2
  rw [chartLocalOffset_eq q ab2.1 ab2.2 t ha]

theorem vertex3_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v3 t = w3.eval owned locals q := by
  change realPoint k2 - chartLocalOffset ab2.1 ab2.2 t =
    realPoint k2 - localOffset q ab2.1 ab2.2
  rw [chartLocalOffset_eq q ab2.1 ab2.2 t ha]

theorem vertex4_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v4 t = w4.eval owned locals q := by
  change realPoint k3 - chartLocalOffset ab2.1 ab2.2 t =
    realPoint k3 - localOffset q ab2.1 ab2.2
  rw [chartLocalOffset_eq q ab2.1 ab2.2 t ha]

theorem vertex5_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v5 t = w5.eval owned locals q := by
  change realPoint k3 - chartLocalOffset ab3.1 ab3.2 t =
    realPoint k3 - localOffset q ab3.1 ab3.2
  rw [chartLocalOffset_eq q ab3.1 ab3.2 t ha]

theorem vertex6_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v6 t = w6.eval owned locals q := by
  change realPoint k4 - chartLocalOffset ab3.1 ab3.2 t =
    realPoint k4 - localOffset q ab3.1 ab3.2
  rw [chartLocalOffset_eq q ab3.1 ab3.2 t ha]

theorem vertex7_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v7 t = w7.eval owned locals q := by
  change realPoint k4 - chartLocalOffset ab0.1 ab0.2 t =
    realPoint k4 - localOffset q ab0.1 ab0.2
  rw [chartLocalOffset_eq q ab0.1 ab0.2 t ha]

theorem vertex8_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v8 t = w8.eval owned locals q := by
  change realPoint k5 - chartLocalOffset ab0.1 ab0.2 t =
    realPoint k5 - localOffset q ab0.1 ab0.2
  rw [chartLocalOffset_eq q ab0.1 ab0.2 t ha]

theorem vertex9_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v9 t = w9.eval owned locals q := by
  change realPoint k6 - chartLocalOffset ab0.1 ab0.2 t =
    realPoint k6 - localOffset q ab0.1 ab0.2
  rw [chartLocalOffset_eq q ab0.1 ab0.2 t ha]

theorem vertex10_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v10 t = w10.eval owned locals q := by
  change realPoint k7 - chartLocalOffset ab0.1 ab0.2 t =
    realPoint k7 - localOffset q ab0.1 ab0.2
  rw [chartLocalOffset_eq q ab0.1 ab0.2 t ha]

theorem vertex11_eval (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    v11 t = w11.eval owned locals q := by
  change realPoint k7 - chartLocalOffset ab1.1 ab1.2 t =
    realPoint k7 - localOffset q ab1.1 ab1.2
  rw [chartLocalOffset_eq q ab1.1 ab1.2 t ha]

theorem locals_strict : ∀ ab ∈ locals, |ab.1| < 1/2 ∧ |ab.2| < 1/2 := by
  intro ab hab
  simp only [locals, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hab
  rcases hab with rfl | rfl | rfl | rfl <;>
    norm_num [ab0, ab1, ab2, ab3, abs_lt]

theorem vertices_checked (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t) :
    MovingDifferenceVerticesCheck owned locals q (vertices t) witnesses := by
  constructor
  · rfl
  · intro vw hv
    simp only [vertices, witnesses, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor
    all_goals norm_num [MovingDifferenceWitness.Valid, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, HullWitness.Valid, owned, locals]
    all_goals first | exact vertex0_eval q t ha | exact vertex1_eval q t ha | exact vertex2_eval q t ha | exact vertex3_eval q t ha | exact vertex4_eval q t ha | exact vertex5_eval q t ha | exact vertex6_eval q t ha | exact vertex7_eval q t ha | exact vertex8_eval q t ha | exact vertex9_eval q t ha | exact vertex10_eval q t ha | exact vertex11_eval q t ha

#print axioms vertices_checked

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
