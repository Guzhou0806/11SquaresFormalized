import ElevenSquare.Tasks.T04.LabelLookupSupport

namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

theorem label_row192 : overlayLabels (192 : Fin 220) = ![13,10,5,7] :=
  label_of_lookup 192 (by decide) _
    ((lookup_chunk6 192 (by decide) (by decide)).trans (by rfl))

theorem label_row193 : overlayLabels (193 : Fin 220) = ![13,10,9,6] :=
  label_of_lookup 193 (by decide) _
    ((lookup_chunk6 193 (by decide) (by decide)).trans (by rfl))

theorem label_row194 : overlayLabels (194 : Fin 220) = ![13,13,4,11] :=
  label_of_lookup 194 (by decide) _
    ((lookup_chunk6 194 (by decide) (by decide)).trans (by rfl))

theorem label_row195 : overlayLabels (195 : Fin 220) = ![13,14,0,7] :=
  label_of_lookup 195 (by decide) _
    ((lookup_chunk6 195 (by decide) (by decide)).trans (by rfl))

theorem label_row196 : overlayLabels (196 : Fin 220) = ![13,14,4,7] :=
  label_of_lookup 196 (by decide) _
    ((lookup_chunk6 196 (by decide) (by decide)).trans (by rfl))

theorem label_row197 : overlayLabels (197 : Fin 220) = ![13,14,4,11] :=
  label_of_lookup 197 (by decide) _
    ((lookup_chunk6 197 (by decide) (by decide)).trans (by rfl))

theorem label_row198 : overlayLabels (198 : Fin 220) = ![13,15,0,7] :=
  label_of_lookup 198 (by decide) _
    ((lookup_chunk6 198 (by decide) (by decide)).trans (by rfl))

theorem label_row199 : overlayLabels (199 : Fin 220) = ![13,15,4,7] :=
  label_of_lookup 199 (by decide) _
    ((lookup_chunk6 199 (by decide) (by decide)).trans (by rfl))

theorem label_row200 : overlayLabels (200 : Fin 220) = ![14,12,8,11] :=
  label_of_lookup 200 (by decide) _
    ((lookup_chunk6 200 (by decide) (by decide)).trans (by rfl))

theorem label_row201 : overlayLabels (201 : Fin 220) = ![14,12,8,15] :=
  label_of_lookup 201 (by decide) _
    ((lookup_chunk6 201 (by decide) (by decide)).trans (by rfl))

theorem label_row202 : overlayLabels (202 : Fin 220) = ![14,13,4,11] :=
  label_of_lookup 202 (by decide) _
    ((lookup_chunk6 202 (by decide) (by decide)).trans (by rfl))

theorem label_row203 : overlayLabels (203 : Fin 220) = ![14,13,8,11] :=
  label_of_lookup 203 (by decide) _
    ((lookup_chunk6 203 (by decide) (by decide)).trans (by rfl))

theorem label_row204 : overlayLabels (204 : Fin 220) = ![14,13,8,15] :=
  label_of_lookup 204 (by decide) _
    ((lookup_chunk6 204 (by decide) (by decide)).trans (by rfl))

theorem label_row205 : overlayLabels (205 : Fin 220) = ![14,14,4,7] :=
  label_of_lookup 205 (by decide) _
    ((lookup_chunk6 205 (by decide) (by decide)).trans (by rfl))

theorem label_row206 : overlayLabels (206 : Fin 220) = ![14,14,4,11] :=
  label_of_lookup 206 (by decide) _
    ((lookup_chunk6 206 (by decide) (by decide)).trans (by rfl))

theorem label_row207 : overlayLabels (207 : Fin 220) = ![14,14,8,11] :=
  label_of_lookup 207 (by decide) _
    ((lookup_chunk6 207 (by decide) (by decide)).trans (by rfl))

theorem label_row208 : overlayLabels (208 : Fin 220) = ![15,8,8,10] :=
  label_of_lookup 208 (by decide) _
    ((lookup_chunk6 208 (by decide) (by decide)).trans (by rfl))

theorem label_row209 : overlayLabels (209 : Fin 220) = ![15,8,8,15] :=
  label_of_lookup 209 (by decide) _
    ((lookup_chunk6 209 (by decide) (by decide)).trans (by rfl))

theorem label_row210 : overlayLabels (210 : Fin 220) = ![15,8,12,10] :=
  label_of_lookup 210 (by decide) _
    ((lookup_chunk6 210 (by decide) (by decide)).trans (by rfl))

theorem label_row211 : overlayLabels (211 : Fin 220) = ![15,8,12,14] :=
  label_of_lookup 211 (by decide) _
    ((lookup_chunk6 211 (by decide) (by decide)).trans (by rfl))

theorem label_row212 : overlayLabels (212 : Fin 220) = ![15,8,12,15] :=
  label_of_lookup 212 (by decide) _
    ((lookup_chunk6 212 (by decide) (by decide)).trans (by rfl))

theorem label_row213 : overlayLabels (213 : Fin 220) = ![15,8,13,10] :=
  label_of_lookup 213 (by decide) _
    ((lookup_chunk6 213 (by decide) (by decide)).trans (by rfl))

theorem label_row214 : overlayLabels (214 : Fin 220) = ![15,8,13,14] :=
  label_of_lookup 214 (by decide) _
    ((lookup_chunk6 214 (by decide) (by decide)).trans (by rfl))

theorem label_row215 : overlayLabels (215 : Fin 220) = ![15,8,13,15] :=
  label_of_lookup 215 (by decide) _
    ((lookup_chunk6 215 (by decide) (by decide)).trans (by rfl))

theorem label_row216 : overlayLabels (216 : Fin 220) = ![15,12,8,15] :=
  label_of_lookup 216 (by decide) _
    ((lookup_chunk6 216 (by decide) (by decide)).trans (by rfl))

theorem label_row217 : overlayLabels (217 : Fin 220) = ![15,12,12,15] :=
  label_of_lookup 217 (by decide) _
    ((lookup_chunk6 217 (by decide) (by decide)).trans (by rfl))

theorem label_row218 : overlayLabels (218 : Fin 220) = ![15,13,8,11] :=
  label_of_lookup 218 (by decide) _
    ((lookup_chunk6 218 (by decide) (by decide)).trans (by rfl))

theorem label_row219 : overlayLabels (219 : Fin 220) = ![15,13,8,15] :=
  label_of_lookup 219 (by decide) _
    ((lookup_chunk6 219 (by decide) (by decide)).trans (by rfl))

end ElevenSquare.Pending.T04LabelLookup
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row192
#print axioms ElevenSquare.Pending.T04LabelLookup.label_row219
