open Types

val try_constraint : mono_type_constraint -> (unit, TypeError.type_error) result

val apply_constraints_poly : level -> quantifiability -> poly_type -> (poly_type, TypeError.type_error) result
