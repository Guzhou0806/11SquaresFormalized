import ElevenSquare.Tasks.T04.LabelLookupSupport

namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

theorem label_row128 : overlayLabels (128 : Fin 220) = ![9,6,5,2] :=
  label_of_lookup 128 (by decide) _
    ((lookup_chunk4 128 (by decide) (by decide)).trans (by rfl))

theorem label_row129 : overlayLabels (129 : Fin 220) = ![9,6,5,5] :=
  label_of_lookup 129 (by decide) _
    ((lookup_chunk4 129 (by decide) (by decide)).trans (by rfl))

theorem label_row130 : overlayLabels (130 : Fin 220) = ![9,6,5,6] :=
  label_of_lookup 130 (by decide) _
    ((lookup_chunk4 130 (by decide) (by decide)).trans (by rfl))

theorem label_row131 : overlayLabels (131 : Fin 220) = ![9,6,6,5] :=
  label_of_lookup 131 (by decide) _
    ((lookup_chunk4 131 (by decide) (by decide)).trans (by rfl))

theorem label_row132 : overlayLabels (132 : Fin 220) = ![9,6,6,6] :=
  label_of_lookup 132 (by decide) _
    ((lookup_chunk4 132 (by decide) (by decide)).trans (by rfl))

theorem label_row133 : overlayLabels (133 : Fin 220) = ![9,6,6,9] :=
  label_of_lookup 133 (by decide) _
    ((lookup_chunk4 133 (by decide) (by decide)).trans (by rfl))

theorem label_row134 : overlayLabels (134 : Fin 220) = ![9,6,9,6] :=
  label_of_lookup 134 (by decide) _
    ((lookup_chunk4 134 (by decide) (by decide)).trans (by rfl))

theorem label_row135 : overlayLabels (135 : Fin 220) = ![9,6,9,9] :=
  label_of_lookup 135 (by decide) _
    ((lookup_chunk4 135 (by decide) (by decide)).trans (by rfl))

theorem label_row136 : overlayLabels (136 : Fin 220) = ![9,9,6,6] :=
  label_of_lookup 136 (by decide) _
    ((lookup_chunk4 136 (by decide) (by decide)).trans (by rfl))

theorem label_row137 : overlayLabels (137 : Fin 220) = ![9,9,6,9] :=
  label_of_lookup 137 (by decide) _
    ((lookup_chunk4 137 (by decide) (by decide)).trans (by rfl))

theorem label_row138 : overlayLabels (138 : Fin 220) = ![9,9,9,6] :=
  label_of_lookup 138 (by decide) _
    ((lookup_chunk4 138 (by decide) (by decide)).trans (by rfl))

theorem label_row139 : overlayLabels (139 : Fin 220) = ![9,9,9,9] :=
  label_of_lookup 139 (by decide) _
    ((lookup_chunk4 139 (by decide) (by decide)).trans (by rfl))

theorem label_row140 : overlayLabels (140 : Fin 220) = ![9,10,5,2] :=
  label_of_lookup 140 (by decide) _
    ((lookup_chunk4 140 (by decide) (by decide)).trans (by rfl))

theorem label_row141 : overlayLabels (141 : Fin 220) = ![9,10,5,6] :=
  label_of_lookup 141 (by decide) _
    ((lookup_chunk4 141 (by decide) (by decide)).trans (by rfl))

theorem label_row142 : overlayLabels (142 : Fin 220) = ![9,10,9,6] :=
  label_of_lookup 142 (by decide) _
    ((lookup_chunk4 142 (by decide) (by decide)).trans (by rfl))

theorem label_row143 : overlayLabels (143 : Fin 220) = ![9,11,5,2] :=
  label_of_lookup 143 (by decide) _
    ((lookup_chunk4 143 (by decide) (by decide)).trans (by rfl))

theorem label_row144 : overlayLabels (144 : Fin 220) = ![9,11,5,5] :=
  label_of_lookup 144 (by decide) _
    ((lookup_chunk4 144 (by decide) (by decide)).trans (by rfl))

theorem label_row145 : overlayLabels (145 : Fin 220) = ![10,8,8,10] :=
  label_of_lookup 145 (by decide) _
    ((lookup_chunk4 145 (by decide) (by decide)).trans (by rfl))

theorem label_row146 : overlayLabels (146 : Fin 220) = ![10,8,8,15] :=
  label_of_lookup 146 (by decide) _
    ((lookup_chunk4 146 (by decide) (by decide)).trans (by rfl))

theorem label_row147 : overlayLabels (147 : Fin 220) = ![10,8,12,10] :=
  label_of_lookup 147 (by decide) _
    ((lookup_chunk4 147 (by decide) (by decide)).trans (by rfl))

theorem label_row148 : overlayLabels (148 : Fin 220) = ![10,8,13,10] :=
  label_of_lookup 148 (by decide) _
    ((lookup_chunk4 148 (by decide) (by decide)).trans (by rfl))

theorem label_row149 : overlayLabels (149 : Fin 220) = ![10,9,9,6] :=
  label_of_lookup 149 (by decide) _
    ((lookup_chunk4 149 (by decide) (by decide)).trans (by rfl))

theorem label_row150 : overlayLabels (150 : Fin 220) = ![10,9,9,10] :=
  label_of_lookup 150 (by decide) _
    ((lookup_chunk4 150 (by decide) (by decide)).trans (by rfl))

theorem label_row151 : overlayLabels (151 : Fin 220) = ![10,9,13,10] :=
  label_of_lookup 151 (by decide) _
    ((lookup_chunk4 151 (by decide) (by decide)).trans (by rfl))

theorem label_row152 : overlayLabels (152 : Fin 220) = ![10,10,4,6] :=
  label_of_lookup 152 (by decide) _
    ((lookup_chunk4 152 (by decide) (by decide)).trans (by rfl))

theorem label_row153 : overlayLabels (153 : Fin 220) = ![10,10,4,11] :=
  label_of_lookup 153 (by decide) _
    ((lookup_chunk4 153 (by decide) (by decide)).trans (by rfl))

theorem label_row154 : overlayLabels (154 : Fin 220) = ![10,10,9,6] :=
  label_of_lookup 154 (by decide) _
    ((lookup_chunk4 154 (by decide) (by decide)).trans (by rfl))

theorem label_row155 : overlayLabels (155 : Fin 220) = ![10,10,9,11] :=
  label_of_lookup 155 (by decide) _
    ((lookup_chunk4 155 (by decide) (by decide)).trans (by rfl))

theorem label_row156 : overlayLabels (156 : Fin 220) = ![10,12,8,10] :=
  label_of_lookup 156 (by decide) _
    ((lookup_chunk4 156 (by decide) (by decide)).trans (by rfl))

theorem label_row157 : overlayLabels (157 : Fin 220) = ![10,12,8,15] :=
  label_of_lookup 157 (by decide) _
    ((lookup_chunk4 157 (by decide) (by decide)).trans (by rfl))

theorem label_row158 : overlayLabels (158 : Fin 220) = ![10,13,4,11] :=
  label_of_lookup 158 (by decide) _
    ((lookup_chunk4 158 (by decide) (by decide)).trans (by rfl))

theorem label_row159 : overlayLabels (159 : Fin 220) = ![10,13,8,10] :=
  label_of_lookup 159 (by decide) _
    ((lookup_chunk4 159 (by decide) (by decide)).trans (by rfl))

end ElevenSquare.Pending.T04LabelLookup
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row128
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row159
