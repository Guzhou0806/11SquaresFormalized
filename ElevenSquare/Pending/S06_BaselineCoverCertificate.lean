import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Pending
noncomputable section

def baselineFlip (h : Halfplane) : Halfplane := ⟨-h.a, -h.b, -h.c⟩

def BaselinePolygonImplicationCheck (source target : Polygon)
    (ws : List BaselineCombination) : Prop :=
  target.length = ws.length ∧
  ∀ hw ∈ target.zip ws, BaselineImplicationCheck source hw.1 hw.2

instance (source target : Polygon) (ws : List BaselineCombination) :
    Decidable (BaselinePolygonImplicationCheck source target ws) := by
  unfold BaselinePolygonImplicationCheck
  infer_instance

theorem baseline_polygon_implication_check_sound (source target : Polygon)
    (ws : List BaselineCombination) (hc : BaselinePolygonImplicationCheck source target ws) :
    source.carrier ⊆ target.carrier := by
  intro p hp
  induction target generalizing ws with
  | nil => intro h hh; simp at hh
  | cons h target ih =>
    cases ws with
    | nil => simp [BaselinePolygonImplicationCheck] at hc
    | cons w ws =>
      have hcheck : BaselineImplicationCheck source h w := hc.2 (h, w) (by simp)
      have htail : BaselinePolygonImplicationCheck source target ws := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro e he
        exact hc.2 e (by simp [he])
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact baseline_implication_check_sound source _ w hcheck p hp
      · exact ih ws htail g hg

inductive BaselineCoverCertificate where
  | empty (w : BaselineCombination)
  | hit (index : ℕ) (w : List BaselineCombination)
  | split (h : Halfplane) (left right : BaselineCoverCertificate)

def BaselineCoverCertificate.Check (source : Polygon) (targets : List Polygon) :
    BaselineCoverCertificate → Prop
  | .empty w => BaselineStrictImplicationCheck source baselineZeroHalfplane w
  | .hit i ws => i < targets.length ∧
    BaselinePolygonImplicationCheck source (targets.getD i []) ws
  | .split h l r => l.Check (h :: source) targets ∧
    r.Check (baselineFlip h :: source) targets

instance (source : Polygon) (targets : List Polygon) (c : BaselineCoverCertificate) :
    Decidable (c.Check source targets) := by
  induction c generalizing source with
  | empty w =>
    exact inferInstanceAs (Decidable (BaselineStrictImplicationCheck _ _ _))
  | hit i w =>
    exact inferInstanceAs (Decidable (_ ∧ BaselinePolygonImplicationCheck _ _ _))
  | split h l r il ir =>
    letI := il (h :: source)
    letI := ir (baselineFlip h :: source)
    exact inferInstanceAs (Decidable (_ ∧ _))

theorem baseline_cover_certificate_sound (source : Polygon) (targets : List Polygon)
    (c : BaselineCoverCertificate) (hc : c.Check source targets)
    (p : Point) (hp : p ∈ source.carrier) : ∃ t ∈ targets, p ∈ t.carrier := by
  induction c generalizing source with
  | empty w =>
    have hf := baseline_strict_implication_check_sound source baselineZeroHalfplane w hc p hp
    norm_num [baselineZeroHalfplane] at hf
  | hit i ws =>
    refine ⟨targets.getD i [], ?_,
      baseline_polygon_implication_check_sound _ _ ws hc.2 hp⟩
    rw [List.getD_eq_getElem targets [] hc.1]
    exact List.get_mem ..
  | split h l r il ir =>
    by_cases hin : h.contains p
    · apply il (h :: source) hc.1
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hin
      · exact hp g hg
    · apply ir (baselineFlip h :: source) hc.2
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · dsimp [baselineFlip, Halfplane.contains] at hin ⊢
        push_cast
        linarith
      · exact hp g hg

end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.baseline_polygon_implication_check_sound
#print axioms ElevenSquare.Pending.baseline_cover_certificate_sound
