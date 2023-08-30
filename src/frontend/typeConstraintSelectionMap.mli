open Types

type t

val add : TypeConstraintID.t -> poly_type_constraint_selection -> unit

val find_opt : TypeConstraintID.t -> poly_type_constraint_selection option
