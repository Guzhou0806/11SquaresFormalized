import ElevenSquare.Tasks.T04.LabelLookupSupport

namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

theorem label_row96 : overlayLabels (96 : Fin 220) = ![7,0,14,12] :=
  label_of_lookup 96 (by decide) _
    ((lookup_chunk3 96 (by decide) (by decide)).trans (by rfl))

theorem label_row97 : overlayLabels (97 : Fin 220) = ![7,0,14,13] :=
  label_of_lookup 97 (by decide) _
    ((lookup_chunk3 97 (by decide) (by decide)).trans (by rfl))

theorem label_row98 : overlayLabels (98 : Fin 220) = ![7,0,15,8] :=
  label_of_lookup 98 (by decide) _
    ((lookup_chunk3 98 (by decide) (by decide)).trans (by rfl))

theorem label_row99 : overlayLabels (99 : Fin 220) = ![7,0,15,12] :=
  label_of_lookup 99 (by decide) _
    ((lookup_chunk3 99 (by decide) (by decide)).trans (by rfl))

theorem label_row100 : overlayLabels (100 : Fin 220) = ![7,0,15,13] :=
  label_of_lookup 100 (by decide) _
    ((lookup_chunk3 100 (by decide) (by decide)).trans (by rfl))

theorem label_row101 : overlayLabels (101 : Fin 220) = ![7,4,10,13] :=
  label_of_lookup 101 (by decide) _
    ((lookup_chunk3 101 (by decide) (by decide)).trans (by rfl))

theorem label_row102 : overlayLabels (102 : Fin 220) = ![7,4,14,12] :=
  label_of_lookup 102 (by decide) _
    ((lookup_chunk3 102 (by decide) (by decide)).trans (by rfl))

theorem label_row103 : overlayLabels (103 : Fin 220) = ![7,4,14,13] :=
  label_of_lookup 103 (by decide) _
    ((lookup_chunk3 103 (by decide) (by decide)).trans (by rfl))

theorem label_row104 : overlayLabels (104 : Fin 220) = ![7,4,14,14] :=
  label_of_lookup 104 (by decide) _
    ((lookup_chunk3 104 (by decide) (by decide)).trans (by rfl))

theorem label_row105 : overlayLabels (105 : Fin 220) = ![7,4,15,13] :=
  label_of_lookup 105 (by decide) _
    ((lookup_chunk3 105 (by decide) (by decide)).trans (by rfl))

theorem label_row106 : overlayLabels (106 : Fin 220) = ![7,5,10,8] :=
  label_of_lookup 106 (by decide) _
    ((lookup_chunk3 106 (by decide) (by decide)).trans (by rfl))

theorem label_row107 : overlayLabels (107 : Fin 220) = ![7,5,10,12] :=
  label_of_lookup 107 (by decide) _
    ((lookup_chunk3 107 (by decide) (by decide)).trans (by rfl))

theorem label_row108 : overlayLabels (108 : Fin 220) = ![7,5,10,13] :=
  label_of_lookup 108 (by decide) _
    ((lookup_chunk3 108 (by decide) (by decide)).trans (by rfl))

theorem label_row109 : overlayLabels (109 : Fin 220) = ![7,5,15,8] :=
  label_of_lookup 109 (by decide) _
    ((lookup_chunk3 109 (by decide) (by decide)).trans (by rfl))

theorem label_row110 : overlayLabels (110 : Fin 220) = ![8,10,0,7] :=
  label_of_lookup 110 (by decide) _
    ((lookup_chunk3 110 (by decide) (by decide)).trans (by rfl))

theorem label_row111 : overlayLabels (111 : Fin 220) = ![8,10,5,2] :=
  label_of_lookup 111 (by decide) _
    ((lookup_chunk3 111 (by decide) (by decide)).trans (by rfl))

theorem label_row112 : overlayLabels (112 : Fin 220) = ![8,10,5,3] :=
  label_of_lookup 112 (by decide) _
    ((lookup_chunk3 112 (by decide) (by decide)).trans (by rfl))

theorem label_row113 : overlayLabels (113 : Fin 220) = ![8,10,5,7] :=
  label_of_lookup 113 (by decide) _
    ((lookup_chunk3 113 (by decide) (by decide)).trans (by rfl))

theorem label_row114 : overlayLabels (114 : Fin 220) = ![8,11,0,2] :=
  label_of_lookup 114 (by decide) _
    ((lookup_chunk3 114 (by decide) (by decide)).trans (by rfl))

theorem label_row115 : overlayLabels (115 : Fin 220) = ![8,11,1,1] :=
  label_of_lookup 115 (by decide) _
    ((lookup_chunk3 115 (by decide) (by decide)).trans (by rfl))

theorem label_row116 : overlayLabels (116 : Fin 220) = ![8,11,1,2] :=
  label_of_lookup 116 (by decide) _
    ((lookup_chunk3 116 (by decide) (by decide)).trans (by rfl))

theorem label_row117 : overlayLabels (117 : Fin 220) = ![8,11,1,3] :=
  label_of_lookup 117 (by decide) _
    ((lookup_chunk3 117 (by decide) (by decide)).trans (by rfl))

theorem label_row118 : overlayLabels (118 : Fin 220) = ![8,11,5,2] :=
  label_of_lookup 118 (by decide) _
    ((lookup_chunk3 118 (by decide) (by decide)).trans (by rfl))

theorem label_row119 : overlayLabels (119 : Fin 220) = ![8,15,0,2] :=
  label_of_lookup 119 (by decide) _
    ((lookup_chunk3 119 (by decide) (by decide)).trans (by rfl))

theorem label_row120 : overlayLabels (120 : Fin 220) = ![8,15,0,3] :=
  label_of_lookup 120 (by decide) _
    ((lookup_chunk3 120 (by decide) (by decide)).trans (by rfl))

theorem label_row121 : overlayLabels (121 : Fin 220) = ![8,15,0,7] :=
  label_of_lookup 121 (by decide) _
    ((lookup_chunk3 121 (by decide) (by decide)).trans (by rfl))

theorem label_row122 : overlayLabels (122 : Fin 220) = ![8,15,1,2] :=
  label_of_lookup 122 (by decide) _
    ((lookup_chunk3 122 (by decide) (by decide)).trans (by rfl))

theorem label_row123 : overlayLabels (123 : Fin 220) = ![8,15,1,3] :=
  label_of_lookup 123 (by decide) _
    ((lookup_chunk3 123 (by decide) (by decide)).trans (by rfl))

theorem label_row124 : overlayLabels (124 : Fin 220) = ![8,15,5,2] :=
  label_of_lookup 124 (by decide) _
    ((lookup_chunk3 124 (by decide) (by decide)).trans (by rfl))

theorem label_row125 : overlayLabels (125 : Fin 220) = ![8,15,5,3] :=
  label_of_lookup 125 (by decide) _
    ((lookup_chunk3 125 (by decide) (by decide)).trans (by rfl))

theorem label_row126 : overlayLabels (126 : Fin 220) = ![8,15,5,7] :=
  label_of_lookup 126 (by decide) _
    ((lookup_chunk3 126 (by decide) (by decide)).trans (by rfl))

theorem label_row127 : overlayLabels (127 : Fin 220) = ![9,6,2,5] :=
  label_of_lookup 127 (by decide) _
    ((lookup_chunk3 127 (by decide) (by decide)).trans (by rfl))

end ElevenSquare.Pending.T04LabelLookup
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row96
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row127
