
open Types
open StaticEnv
open TypeError

val typecheck_signature : Typeenv.t -> untyped_signature -> (signature abstracted, type_error) result

val main : Typeenv.t -> (signature abstracted) option -> untyped_binding list -> (StructSig.t abstracted * binding list * mono_type_constraint_reference list * poly_type_constraint_selection_map, type_error) result
