open Types

type t

val add : FreeID.t -> mono_type -> unit
val find_opt : FreeID.t -> mono_type option
val freeze : unit -> t
val restore : t -> unit
