open StaticEnv
open Types

val try_solving : mono_type_constraint_reference list -> poly_type_constraint_selection_map -> (unit, TypeError.type_error) result

val apply_constraints_mono : mono_type_constraint_reference list -> poly_type_constraint_selection_map -> (unit, TypeError.type_error) result

val apply_constraints_poly : level -> quantifiability -> poly_type_constraint_selection_map -> poly_type -> (poly_type, TypeError.type_error) result

val apply_constraints_ssig : poly_type_constraint_selection_map -> StructSig.t -> (StructSig.t, TypeError.type_error) result
