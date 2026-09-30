import ElevenSquare.Tasks.T04.LabelLookupSupport

namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

theorem label_row64 : overlayLabels (64 : Fin 220) = ![5,5,6,4] :=
  label_of_lookup 64 (by decide) _
    ((lookup_chunk2 64 (by decide) (by decide)).trans (by rfl))

theorem label_row65 : overlayLabels (65 : Fin 220) = ![5,5,6,9] :=
  label_of_lookup 65 (by decide) _
    ((lookup_chunk2 65 (by decide) (by decide)).trans (by rfl))

theorem label_row66 : overlayLabels (66 : Fin 220) = ![5,5,11,4] :=
  label_of_lookup 66 (by decide) _
    ((lookup_chunk2 66 (by decide) (by decide)).trans (by rfl))

theorem label_row67 : overlayLabels (67 : Fin 220) = ![5,5,11,9] :=
  label_of_lookup 67 (by decide) _
    ((lookup_chunk2 67 (by decide) (by decide)).trans (by rfl))

theorem label_row68 : overlayLabels (68 : Fin 220) = ![5,6,2,5] :=
  label_of_lookup 68 (by decide) _
    ((lookup_chunk2 68 (by decide) (by decide)).trans (by rfl))

theorem label_row69 : overlayLabels (69 : Fin 220) = ![5,6,6,5] :=
  label_of_lookup 69 (by decide) _
    ((lookup_chunk2 69 (by decide) (by decide)).trans (by rfl))

theorem label_row70 : overlayLabels (70 : Fin 220) = ![5,6,6,9] :=
  label_of_lookup 70 (by decide) _
    ((lookup_chunk2 70 (by decide) (by decide)).trans (by rfl))

theorem label_row71 : overlayLabels (71 : Fin 220) = ![5,7,2,5] :=
  label_of_lookup 71 (by decide) _
    ((lookup_chunk2 71 (by decide) (by decide)).trans (by rfl))

theorem label_row72 : overlayLabels (72 : Fin 220) = ![5,7,3,5] :=
  label_of_lookup 72 (by decide) _
    ((lookup_chunk2 72 (by decide) (by decide)).trans (by rfl))

theorem label_row73 : overlayLabels (73 : Fin 220) = ![5,7,7,0] :=
  label_of_lookup 73 (by decide) _
    ((lookup_chunk2 73 (by decide) (by decide)).trans (by rfl))

theorem label_row74 : overlayLabels (74 : Fin 220) = ![5,7,7,5] :=
  label_of_lookup 74 (by decide) _
    ((lookup_chunk2 74 (by decide) (by decide)).trans (by rfl))

theorem label_row75 : overlayLabels (75 : Fin 220) = ![6,4,10,10] :=
  label_of_lookup 75 (by decide) _
    ((lookup_chunk2 75 (by decide) (by decide)).trans (by rfl))

theorem label_row76 : overlayLabels (76 : Fin 220) = ![6,4,10,13] :=
  label_of_lookup 76 (by decide) _
    ((lookup_chunk2 76 (by decide) (by decide)).trans (by rfl))

theorem label_row77 : overlayLabels (77 : Fin 220) = ![6,5,6,9] :=
  label_of_lookup 77 (by decide) _
    ((lookup_chunk2 77 (by decide) (by decide)).trans (by rfl))

theorem label_row78 : overlayLabels (78 : Fin 220) = ![6,5,10,9] :=
  label_of_lookup 78 (by decide) _
    ((lookup_chunk2 78 (by decide) (by decide)).trans (by rfl))

theorem label_row79 : overlayLabels (79 : Fin 220) = ![6,5,10,13] :=
  label_of_lookup 79 (by decide) _
    ((lookup_chunk2 79 (by decide) (by decide)).trans (by rfl))

theorem label_row80 : overlayLabels (80 : Fin 220) = ![6,6,6,6] :=
  label_of_lookup 80 (by decide) _
    ((lookup_chunk2 80 (by decide) (by decide)).trans (by rfl))

theorem label_row81 : overlayLabels (81 : Fin 220) = ![6,6,6,9] :=
  label_of_lookup 81 (by decide) _
    ((lookup_chunk2 81 (by decide) (by decide)).trans (by rfl))

theorem label_row82 : overlayLabels (82 : Fin 220) = ![6,6,9,6] :=
  label_of_lookup 82 (by decide) _
    ((lookup_chunk2 82 (by decide) (by decide)).trans (by rfl))

theorem label_row83 : overlayLabels (83 : Fin 220) = ![6,6,9,9] :=
  label_of_lookup 83 (by decide) _
    ((lookup_chunk2 83 (by decide) (by decide)).trans (by rfl))

theorem label_row84 : overlayLabels (84 : Fin 220) = ![6,9,6,6] :=
  label_of_lookup 84 (by decide) _
    ((lookup_chunk2 84 (by decide) (by decide)).trans (by rfl))

theorem label_row85 : overlayLabels (85 : Fin 220) = ![6,9,6,9] :=
  label_of_lookup 85 (by decide) _
    ((lookup_chunk2 85 (by decide) (by decide)).trans (by rfl))

theorem label_row86 : overlayLabels (86 : Fin 220) = ![6,9,9,6] :=
  label_of_lookup 86 (by decide) _
    ((lookup_chunk2 86 (by decide) (by decide)).trans (by rfl))

theorem label_row87 : overlayLabels (87 : Fin 220) = ![6,9,9,9] :=
  label_of_lookup 87 (by decide) _
    ((lookup_chunk2 87 (by decide) (by decide)).trans (by rfl))

theorem label_row88 : overlayLabels (88 : Fin 220) = ![6,9,9,10] :=
  label_of_lookup 88 (by decide) _
    ((lookup_chunk2 88 (by decide) (by decide)).trans (by rfl))

theorem label_row89 : overlayLabels (89 : Fin 220) = ![6,9,10,9] :=
  label_of_lookup 89 (by decide) _
    ((lookup_chunk2 89 (by decide) (by decide)).trans (by rfl))

theorem label_row90 : overlayLabels (90 : Fin 220) = ![6,9,10,10] :=
  label_of_lookup 90 (by decide) _
    ((lookup_chunk2 90 (by decide) (by decide)).trans (by rfl))

theorem label_row91 : overlayLabels (91 : Fin 220) = ![6,9,10,13] :=
  label_of_lookup 91 (by decide) _
    ((lookup_chunk2 91 (by decide) (by decide)).trans (by rfl))

theorem label_row92 : overlayLabels (92 : Fin 220) = ![6,9,13,10] :=
  label_of_lookup 92 (by decide) _
    ((lookup_chunk2 92 (by decide) (by decide)).trans (by rfl))

theorem label_row93 : overlayLabels (93 : Fin 220) = ![7,0,10,8] :=
  label_of_lookup 93 (by decide) _
    ((lookup_chunk2 93 (by decide) (by decide)).trans (by rfl))

theorem label_row94 : overlayLabels (94 : Fin 220) = ![7,0,10,12] :=
  label_of_lookup 94 (by decide) _
    ((lookup_chunk2 94 (by decide) (by decide)).trans (by rfl))

theorem label_row95 : overlayLabels (95 : Fin 220) = ![7,0,10,13] :=
  label_of_lookup 95 (by decide) _
    ((lookup_chunk2 95 (by decide) (by decide)).trans (by rfl))

end ElevenSquare.Pending.T04LabelLookup
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row64
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row95
