
open Types
open StaticEnv
open TypeError

val typecheck_signature : Typeenv.t -> untyped_signature -> (signature abstracted, type_error) result

val main : Typeenv.t -> (signature abstracted) option -> untyped_binding list -> (StructSig.t abstracted * binding list * mono_type_constraint_reference list * TypeConstraintID.t list, type_error) result
