import ElevenSquare.Tasks.T04.LabelLookupSupport

namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

theorem label_row32 : overlayLabels (32 : Fin 220) = ![2,5,11,9] :=
  label_of_lookup 32 (by decide) _
    ((lookup_chunk1 32 (by decide) (by decide)).trans (by rfl))

theorem label_row33 : overlayLabels (33 : Fin 220) = ![2,5,15,8] :=
  label_of_lookup 33 (by decide) _
    ((lookup_chunk1 33 (by decide) (by decide)).trans (by rfl))

theorem label_row34 : overlayLabels (34 : Fin 220) = ![3,0,15,8] :=
  label_of_lookup 34 (by decide) _
    ((lookup_chunk1 34 (by decide) (by decide)).trans (by rfl))

theorem label_row35 : overlayLabels (35 : Fin 220) = ![3,0,15,12] :=
  label_of_lookup 35 (by decide) _
    ((lookup_chunk1 35 (by decide) (by decide)).trans (by rfl))

theorem label_row36 : overlayLabels (36 : Fin 220) = ![3,1,11,8] :=
  label_of_lookup 36 (by decide) _
    ((lookup_chunk1 36 (by decide) (by decide)).trans (by rfl))

theorem label_row37 : overlayLabels (37 : Fin 220) = ![3,1,15,8] :=
  label_of_lookup 37 (by decide) _
    ((lookup_chunk1 37 (by decide) (by decide)).trans (by rfl))

theorem label_row38 : overlayLabels (38 : Fin 220) = ![3,5,10,8] :=
  label_of_lookup 38 (by decide) _
    ((lookup_chunk1 38 (by decide) (by decide)).trans (by rfl))

theorem label_row39 : overlayLabels (39 : Fin 220) = ![3,5,15,8] :=
  label_of_lookup 39 (by decide) _
    ((lookup_chunk1 39 (by decide) (by decide)).trans (by rfl))

theorem label_row40 : overlayLabels (40 : Fin 220) = ![4,6,2,5] :=
  label_of_lookup 40 (by decide) _
    ((lookup_chunk1 40 (by decide) (by decide)).trans (by rfl))

theorem label_row41 : overlayLabels (41 : Fin 220) = ![4,6,5,5] :=
  label_of_lookup 41 (by decide) _
    ((lookup_chunk1 41 (by decide) (by decide)).trans (by rfl))

theorem label_row42 : overlayLabels (42 : Fin 220) = ![4,7,1,1] :=
  label_of_lookup 42 (by decide) _
    ((lookup_chunk1 42 (by decide) (by decide)).trans (by rfl))

theorem label_row43 : overlayLabels (43 : Fin 220) = ![4,7,2,0] :=
  label_of_lookup 43 (by decide) _
    ((lookup_chunk1 43 (by decide) (by decide)).trans (by rfl))

theorem label_row44 : overlayLabels (44 : Fin 220) = ![4,7,2,1] :=
  label_of_lookup 44 (by decide) _
    ((lookup_chunk1 44 (by decide) (by decide)).trans (by rfl))

theorem label_row45 : overlayLabels (45 : Fin 220) = ![4,7,2,5] :=
  label_of_lookup 45 (by decide) _
    ((lookup_chunk1 45 (by decide) (by decide)).trans (by rfl))

theorem label_row46 : overlayLabels (46 : Fin 220) = ![4,7,3,1] :=
  label_of_lookup 46 (by decide) _
    ((lookup_chunk1 46 (by decide) (by decide)).trans (by rfl))

theorem label_row47 : overlayLabels (47 : Fin 220) = ![4,11,1,1] :=
  label_of_lookup 47 (by decide) _
    ((lookup_chunk1 47 (by decide) (by decide)).trans (by rfl))

theorem label_row48 : overlayLabels (48 : Fin 220) = ![4,11,1,2] :=
  label_of_lookup 48 (by decide) _
    ((lookup_chunk1 48 (by decide) (by decide)).trans (by rfl))

theorem label_row49 : overlayLabels (49 : Fin 220) = ![4,11,2,1] :=
  label_of_lookup 49 (by decide) _
    ((lookup_chunk1 49 (by decide) (by decide)).trans (by rfl))

theorem label_row50 : overlayLabels (50 : Fin 220) = ![4,11,2,2] :=
  label_of_lookup 50 (by decide) _
    ((lookup_chunk1 50 (by decide) (by decide)).trans (by rfl))

theorem label_row51 : overlayLabels (51 : Fin 220) = ![4,11,2,5] :=
  label_of_lookup 51 (by decide) _
    ((lookup_chunk1 51 (by decide) (by decide)).trans (by rfl))

theorem label_row52 : overlayLabels (52 : Fin 220) = ![4,11,5,2] :=
  label_of_lookup 52 (by decide) _
    ((lookup_chunk1 52 (by decide) (by decide)).trans (by rfl))

theorem label_row53 : overlayLabels (53 : Fin 220) = ![4,11,5,5] :=
  label_of_lookup 53 (by decide) _
    ((lookup_chunk1 53 (by decide) (by decide)).trans (by rfl))

theorem label_row54 : overlayLabels (54 : Fin 220) = ![5,2,2,5] :=
  label_of_lookup 54 (by decide) _
    ((lookup_chunk1 54 (by decide) (by decide)).trans (by rfl))

theorem label_row55 : overlayLabels (55 : Fin 220) = ![5,2,6,4] :=
  label_of_lookup 55 (by decide) _
    ((lookup_chunk1 55 (by decide) (by decide)).trans (by rfl))

theorem label_row56 : overlayLabels (56 : Fin 220) = ![5,2,6,5] :=
  label_of_lookup 56 (by decide) _
    ((lookup_chunk1 56 (by decide) (by decide)).trans (by rfl))

theorem label_row57 : overlayLabels (57 : Fin 220) = ![5,2,6,9] :=
  label_of_lookup 57 (by decide) _
    ((lookup_chunk1 57 (by decide) (by decide)).trans (by rfl))

theorem label_row58 : overlayLabels (58 : Fin 220) = ![5,2,7,0] :=
  label_of_lookup 58 (by decide) _
    ((lookup_chunk1 58 (by decide) (by decide)).trans (by rfl))

theorem label_row59 : overlayLabels (59 : Fin 220) = ![5,2,7,4] :=
  label_of_lookup 59 (by decide) _
    ((lookup_chunk1 59 (by decide) (by decide)).trans (by rfl))

theorem label_row60 : overlayLabels (60 : Fin 220) = ![5,2,7,5] :=
  label_of_lookup 60 (by decide) _
    ((lookup_chunk1 60 (by decide) (by decide)).trans (by rfl))

theorem label_row61 : overlayLabels (61 : Fin 220) = ![5,2,11,4] :=
  label_of_lookup 61 (by decide) _
    ((lookup_chunk1 61 (by decide) (by decide)).trans (by rfl))

theorem label_row62 : overlayLabels (62 : Fin 220) = ![5,3,7,0] :=
  label_of_lookup 62 (by decide) _
    ((lookup_chunk1 62 (by decide) (by decide)).trans (by rfl))

theorem label_row63 : overlayLabels (63 : Fin 220) = ![5,3,7,5] :=
  label_of_lookup 63 (by decide) _
    ((lookup_chunk1 63 (by decide) (by decide)).trans (by rfl))

end ElevenSquare.Pending.T04LabelLookup
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row32
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row63
