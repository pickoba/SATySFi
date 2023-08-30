open Types

val make_group : mono_type_constraint_reference list -> TypeConstraintID.t list -> mono_type_constraint_reference list

val try_solving : mono_type_constraint_reference list -> TypeConstraintID.t list -> (unit, TypeError.type_error) result

val apply_constraints_mono : mono_type_constraint_reference list -> (unit, TypeError.type_error) result

val apply_constraints_poly : level -> quantifiability -> poly_type -> (poly_type, TypeError.type_error) result
