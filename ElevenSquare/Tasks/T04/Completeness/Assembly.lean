import ElevenSquare.Tasks.T04.Completeness.First0
import ElevenSquare.Tasks.T04.Completeness.First1
import ElevenSquare.Tasks.T04.Completeness.First2
import ElevenSquare.Tasks.T04.Completeness.First3
import ElevenSquare.Tasks.T04.Completeness.First4
import ElevenSquare.Tasks.T04.Completeness.First5
import ElevenSquare.Tasks.T04.Completeness.First6
import ElevenSquare.Tasks.T04.Completeness.First7
import ElevenSquare.Tasks.T04.Completeness.First8
import ElevenSquare.Tasks.T04.Completeness.First9
import ElevenSquare.Tasks.T04.Completeness.First10
import ElevenSquare.Tasks.T04.Completeness.First11
import ElevenSquare.Tasks.T04.Completeness.First12
import ElevenSquare.Tasks.T04.Completeness.First13
import ElevenSquare.Tasks.T04.Completeness.First14
import ElevenSquare.Tasks.T04.Completeness.First15

namespace ElevenSquare.Pending.T04Completeness

theorem inventory_complete (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p)) :
    ∃ r : Fin 220, overlayLabels r = labels := by
  generalize he : labels 0 = first
  fin_cases first
  · exact complete_0 labels p h he
  · exact complete_1 labels p h he
  · exact complete_2 labels p h he
  · exact complete_3 labels p h he
  · exact complete_4 labels p h he
  · exact complete_5 labels p h he
  · exact complete_6 labels p h he
  · exact complete_7 labels p h he
  · exact complete_8 labels p h he
  · exact complete_9 labels p h he
  · exact complete_10 labels p h he
  · exact complete_11 labels p h he
  · exact complete_12 labels p h he
  · exact complete_13 labels p h he
  · exact complete_14 labels p h he
  · exact complete_15 labels p h he

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.inventory_complete
