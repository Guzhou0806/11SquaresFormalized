import ElevenSquare.Tasks.T04.LabelLookupSupport

namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

theorem label_row0 : overlayLabels (0 : Fin 220) = ![0,2,7,0] :=
  label_of_lookup 0 (by decide) _
    ((lookup_chunk0 0 (by decide) (by decide)).trans (by rfl))

theorem label_row1 : overlayLabels (1 : Fin 220) = ![0,2,7,4] :=
  label_of_lookup 1 (by decide) _
    ((lookup_chunk0 1 (by decide) (by decide)).trans (by rfl))

theorem label_row2 : overlayLabels (2 : Fin 220) = ![0,3,3,0] :=
  label_of_lookup 2 (by decide) _
    ((lookup_chunk0 2 (by decide) (by decide)).trans (by rfl))

theorem label_row3 : overlayLabels (3 : Fin 220) = ![0,3,7,0] :=
  label_of_lookup 3 (by decide) _
    ((lookup_chunk0 3 (by decide) (by decide)).trans (by rfl))

theorem label_row4 : overlayLabels (4 : Fin 220) = ![0,7,2,0] :=
  label_of_lookup 4 (by decide) _
    ((lookup_chunk0 4 (by decide) (by decide)).trans (by rfl))

theorem label_row5 : overlayLabels (5 : Fin 220) = ![0,7,2,1] :=
  label_of_lookup 5 (by decide) _
    ((lookup_chunk0 5 (by decide) (by decide)).trans (by rfl))

theorem label_row6 : overlayLabels (6 : Fin 220) = ![0,7,2,5] :=
  label_of_lookup 6 (by decide) _
    ((lookup_chunk0 6 (by decide) (by decide)).trans (by rfl))

theorem label_row7 : overlayLabels (7 : Fin 220) = ![0,7,3,0] :=
  label_of_lookup 7 (by decide) _
    ((lookup_chunk0 7 (by decide) (by decide)).trans (by rfl))

theorem label_row8 : overlayLabels (8 : Fin 220) = ![0,7,3,1] :=
  label_of_lookup 8 (by decide) _
    ((lookup_chunk0 8 (by decide) (by decide)).trans (by rfl))

theorem label_row9 : overlayLabels (9 : Fin 220) = ![0,7,3,5] :=
  label_of_lookup 9 (by decide) _
    ((lookup_chunk0 9 (by decide) (by decide)).trans (by rfl))

theorem label_row10 : overlayLabels (10 : Fin 220) = ![0,7,7,0] :=
  label_of_lookup 10 (by decide) _
    ((lookup_chunk0 10 (by decide) (by decide)).trans (by rfl))

theorem label_row11 : overlayLabels (11 : Fin 220) = ![0,7,7,5] :=
  label_of_lookup 11 (by decide) _
    ((lookup_chunk0 11 (by decide) (by decide)).trans (by rfl))

theorem label_row12 : overlayLabels (12 : Fin 220) = ![1,1,7,4] :=
  label_of_lookup 12 (by decide) _
    ((lookup_chunk0 12 (by decide) (by decide)).trans (by rfl))

theorem label_row13 : overlayLabels (13 : Fin 220) = ![1,1,11,4] :=
  label_of_lookup 13 (by decide) _
    ((lookup_chunk0 13 (by decide) (by decide)).trans (by rfl))

theorem label_row14 : overlayLabels (14 : Fin 220) = ![1,1,11,8] :=
  label_of_lookup 14 (by decide) _
    ((lookup_chunk0 14 (by decide) (by decide)).trans (by rfl))

theorem label_row15 : overlayLabels (15 : Fin 220) = ![1,2,7,0] :=
  label_of_lookup 15 (by decide) _
    ((lookup_chunk0 15 (by decide) (by decide)).trans (by rfl))

theorem label_row16 : overlayLabels (16 : Fin 220) = ![1,2,7,4] :=
  label_of_lookup 16 (by decide) _
    ((lookup_chunk0 16 (by decide) (by decide)).trans (by rfl))

theorem label_row17 : overlayLabels (17 : Fin 220) = ![1,2,11,4] :=
  label_of_lookup 17 (by decide) _
    ((lookup_chunk0 17 (by decide) (by decide)).trans (by rfl))

theorem label_row18 : overlayLabels (18 : Fin 220) = ![1,3,7,0] :=
  label_of_lookup 18 (by decide) _
    ((lookup_chunk0 18 (by decide) (by decide)).trans (by rfl))

theorem label_row19 : overlayLabels (19 : Fin 220) = ![1,3,7,4] :=
  label_of_lookup 19 (by decide) _
    ((lookup_chunk0 19 (by decide) (by decide)).trans (by rfl))

theorem label_row20 : overlayLabels (20 : Fin 220) = ![2,0,11,8] :=
  label_of_lookup 20 (by decide) _
    ((lookup_chunk0 20 (by decide) (by decide)).trans (by rfl))

theorem label_row21 : overlayLabels (21 : Fin 220) = ![2,0,15,8] :=
  label_of_lookup 21 (by decide) _
    ((lookup_chunk0 21 (by decide) (by decide)).trans (by rfl))

theorem label_row22 : overlayLabels (22 : Fin 220) = ![2,1,11,4] :=
  label_of_lookup 22 (by decide) _
    ((lookup_chunk0 22 (by decide) (by decide)).trans (by rfl))

theorem label_row23 : overlayLabels (23 : Fin 220) = ![2,1,11,8] :=
  label_of_lookup 23 (by decide) _
    ((lookup_chunk0 23 (by decide) (by decide)).trans (by rfl))

theorem label_row24 : overlayLabels (24 : Fin 220) = ![2,1,15,8] :=
  label_of_lookup 24 (by decide) _
    ((lookup_chunk0 24 (by decide) (by decide)).trans (by rfl))

theorem label_row25 : overlayLabels (25 : Fin 220) = ![2,2,11,4] :=
  label_of_lookup 25 (by decide) _
    ((lookup_chunk0 25 (by decide) (by decide)).trans (by rfl))

theorem label_row26 : overlayLabels (26 : Fin 220) = ![2,5,6,9] :=
  label_of_lookup 26 (by decide) _
    ((lookup_chunk0 26 (by decide) (by decide)).trans (by rfl))

theorem label_row27 : overlayLabels (27 : Fin 220) = ![2,5,10,8] :=
  label_of_lookup 27 (by decide) _
    ((lookup_chunk0 27 (by decide) (by decide)).trans (by rfl))

theorem label_row28 : overlayLabels (28 : Fin 220) = ![2,5,10,9] :=
  label_of_lookup 28 (by decide) _
    ((lookup_chunk0 28 (by decide) (by decide)).trans (by rfl))

theorem label_row29 : overlayLabels (29 : Fin 220) = ![2,5,10,13] :=
  label_of_lookup 29 (by decide) _
    ((lookup_chunk0 29 (by decide) (by decide)).trans (by rfl))

theorem label_row30 : overlayLabels (30 : Fin 220) = ![2,5,11,4] :=
  label_of_lookup 30 (by decide) _
    ((lookup_chunk0 30 (by decide) (by decide)).trans (by rfl))

theorem label_row31 : overlayLabels (31 : Fin 220) = ![2,5,11,8] :=
  label_of_lookup 31 (by decide) _
    ((lookup_chunk0 31 (by decide) (by decide)).trans (by rfl))

end ElevenSquare.Pending.T04LabelLookup
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row0
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row31
