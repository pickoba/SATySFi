open Types

module MapImpl = Map.Make(TypeConstraintID)

type t = poly_type_constraint_selection MapImpl.t

let current_map = ref MapImpl.empty

let add (id : TypeConstraintID.t) (sel : poly_type_constraint_selection) : unit =
  current_map := MapImpl.add id sel !current_map

let find_opt (id : TypeConstraintID.t) : poly_type_constraint_selection option =
  MapImpl.find_opt id !current_map
