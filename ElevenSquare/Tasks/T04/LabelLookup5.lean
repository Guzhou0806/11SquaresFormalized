import ElevenSquare.Tasks.T04.LabelLookupSupport

namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

theorem label_row160 : overlayLabels (160 : Fin 220) = ![10,13,8,11] :=
  label_of_lookup 160 (by decide) _
    ((lookup_chunk5 160 (by decide) (by decide)).trans (by rfl))

theorem label_row161 : overlayLabels (161 : Fin 220) = ![10,13,8,15] :=
  label_of_lookup 161 (by decide) _
    ((lookup_chunk5 161 (by decide) (by decide)).trans (by rfl))

theorem label_row162 : overlayLabels (162 : Fin 220) = ![10,13,9,6] :=
  label_of_lookup 162 (by decide) _
    ((lookup_chunk5 162 (by decide) (by decide)).trans (by rfl))

theorem label_row163 : overlayLabels (163 : Fin 220) = ![10,13,9,10] :=
  label_of_lookup 163 (by decide) _
    ((lookup_chunk5 163 (by decide) (by decide)).trans (by rfl))

theorem label_row164 : overlayLabels (164 : Fin 220) = ![10,13,9,11] :=
  label_of_lookup 164 (by decide) _
    ((lookup_chunk5 164 (by decide) (by decide)).trans (by rfl))

theorem label_row165 : overlayLabels (165 : Fin 220) = ![10,13,13,10] :=
  label_of_lookup 165 (by decide) _
    ((lookup_chunk5 165 (by decide) (by decide)).trans (by rfl))

theorem label_row166 : overlayLabels (166 : Fin 220) = ![11,4,10,10] :=
  label_of_lookup 166 (by decide) _
    ((lookup_chunk5 166 (by decide) (by decide)).trans (by rfl))

theorem label_row167 : overlayLabels (167 : Fin 220) = ![11,4,10,13] :=
  label_of_lookup 167 (by decide) _
    ((lookup_chunk5 167 (by decide) (by decide)).trans (by rfl))

theorem label_row168 : overlayLabels (168 : Fin 220) = ![11,4,13,10] :=
  label_of_lookup 168 (by decide) _
    ((lookup_chunk5 168 (by decide) (by decide)).trans (by rfl))

theorem label_row169 : overlayLabels (169 : Fin 220) = ![11,4,13,13] :=
  label_of_lookup 169 (by decide) _
    ((lookup_chunk5 169 (by decide) (by decide)).trans (by rfl))

theorem label_row170 : overlayLabels (170 : Fin 220) = ![11,4,13,14] :=
  label_of_lookup 170 (by decide) _
    ((lookup_chunk5 170 (by decide) (by decide)).trans (by rfl))

theorem label_row171 : overlayLabels (171 : Fin 220) = ![11,4,14,13] :=
  label_of_lookup 171 (by decide) _
    ((lookup_chunk5 171 (by decide) (by decide)).trans (by rfl))

theorem label_row172 : overlayLabels (172 : Fin 220) = ![11,4,14,14] :=
  label_of_lookup 172 (by decide) _
    ((lookup_chunk5 172 (by decide) (by decide)).trans (by rfl))

theorem label_row173 : overlayLabels (173 : Fin 220) = ![11,8,12,14] :=
  label_of_lookup 173 (by decide) _
    ((lookup_chunk5 173 (by decide) (by decide)).trans (by rfl))

theorem label_row174 : overlayLabels (174 : Fin 220) = ![11,8,13,10] :=
  label_of_lookup 174 (by decide) _
    ((lookup_chunk5 174 (by decide) (by decide)).trans (by rfl))

theorem label_row175 : overlayLabels (175 : Fin 220) = ![11,8,13,14] :=
  label_of_lookup 175 (by decide) _
    ((lookup_chunk5 175 (by decide) (by decide)).trans (by rfl))

theorem label_row176 : overlayLabels (176 : Fin 220) = ![11,8,13,15] :=
  label_of_lookup 176 (by decide) _
    ((lookup_chunk5 176 (by decide) (by decide)).trans (by rfl))

theorem label_row177 : overlayLabels (177 : Fin 220) = ![11,8,14,14] :=
  label_of_lookup 177 (by decide) _
    ((lookup_chunk5 177 (by decide) (by decide)).trans (by rfl))

theorem label_row178 : overlayLabels (178 : Fin 220) = ![11,9,10,10] :=
  label_of_lookup 178 (by decide) _
    ((lookup_chunk5 178 (by decide) (by decide)).trans (by rfl))

theorem label_row179 : overlayLabels (179 : Fin 220) = ![11,9,13,10] :=
  label_of_lookup 179 (by decide) _
    ((lookup_chunk5 179 (by decide) (by decide)).trans (by rfl))

theorem label_row180 : overlayLabels (180 : Fin 220) = ![12,10,0,7] :=
  label_of_lookup 180 (by decide) _
    ((lookup_chunk5 180 (by decide) (by decide)).trans (by rfl))

theorem label_row181 : overlayLabels (181 : Fin 220) = ![12,10,5,7] :=
  label_of_lookup 181 (by decide) _
    ((lookup_chunk5 181 (by decide) (by decide)).trans (by rfl))

theorem label_row182 : overlayLabels (182 : Fin 220) = ![12,14,0,7] :=
  label_of_lookup 182 (by decide) _
    ((lookup_chunk5 182 (by decide) (by decide)).trans (by rfl))

theorem label_row183 : overlayLabels (183 : Fin 220) = ![12,14,4,7] :=
  label_of_lookup 183 (by decide) _
    ((lookup_chunk5 183 (by decide) (by decide)).trans (by rfl))

theorem label_row184 : overlayLabels (184 : Fin 220) = ![12,15,0,3] :=
  label_of_lookup 184 (by decide) _
    ((lookup_chunk5 184 (by decide) (by decide)).trans (by rfl))

theorem label_row185 : overlayLabels (185 : Fin 220) = ![12,15,0,7] :=
  label_of_lookup 185 (by decide) _
    ((lookup_chunk5 185 (by decide) (by decide)).trans (by rfl))

theorem label_row186 : overlayLabels (186 : Fin 220) = ![13,10,0,7] :=
  label_of_lookup 186 (by decide) _
    ((lookup_chunk5 186 (by decide) (by decide)).trans (by rfl))

theorem label_row187 : overlayLabels (187 : Fin 220) = ![13,10,4,6] :=
  label_of_lookup 187 (by decide) _
    ((lookup_chunk5 187 (by decide) (by decide)).trans (by rfl))

theorem label_row188 : overlayLabels (188 : Fin 220) = ![13,10,4,7] :=
  label_of_lookup 188 (by decide) _
    ((lookup_chunk5 188 (by decide) (by decide)).trans (by rfl))

theorem label_row189 : overlayLabels (189 : Fin 220) = ![13,10,4,11] :=
  label_of_lookup 189 (by decide) _
    ((lookup_chunk5 189 (by decide) (by decide)).trans (by rfl))

theorem label_row190 : overlayLabels (190 : Fin 220) = ![13,10,5,2] :=
  label_of_lookup 190 (by decide) _
    ((lookup_chunk5 190 (by decide) (by decide)).trans (by rfl))

theorem label_row191 : overlayLabels (191 : Fin 220) = ![13,10,5,6] :=
  label_of_lookup 191 (by decide) _
    ((lookup_chunk5 191 (by decide) (by decide)).trans (by rfl))

end ElevenSquare.Pending.T04LabelLookup
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row160
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row191
