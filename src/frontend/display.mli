open Types

val collect_ids_mono : mono_type -> DisplayMap.t -> DisplayMap.t

val collect_ids_mono_row : mono_row -> DisplayMap.t -> DisplayMap.t

val show_mono_type_by_map : DisplayMap.t -> mono_type -> string

val show_mono_row_by_map : DisplayMap.t -> mono_row -> string option

val show_mono_type : mono_type -> string

val show_mono_type_double : mono_type -> mono_type -> (string * string)

val show_poly_type : poly_type -> string

val show_poly_macro_type : poly_macro_type -> string

val show_mono_type_constraint_expr : mono_type_constraint_expr -> string

val show_mono_type_constraint_branch : mono_type_constraint_branch -> string

val show_mono_type_constraint : mono_type_constraint -> string

val show_poly_type_constraint : DisplayMap.t -> poly_type_constraint -> string
