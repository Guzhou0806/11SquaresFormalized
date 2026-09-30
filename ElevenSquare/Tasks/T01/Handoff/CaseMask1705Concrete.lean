import ElevenSquare.Tasks.T01.Handoff.CaseMask1705Variable

namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending

theorem case_mask_1705 :
    caseMask ⟨1705, by decide⟩ =
      ({0, 2, 3, 4, 5, 7, 8, 9, 10, 13, 15} : Finset (Fin 16)) :=
  case_mask_1705_of_val ⟨1705, by decide⟩ rfl

end ElevenSquare.Tasks.T01.Handoff

#print axioms ElevenSquare.Tasks.T01.Handoff.case_mask_1705
