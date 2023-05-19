open Types

type t

val add : FreeRowID.t -> mono_row -> unit
val find_opt : FreeRowID.t -> mono_row option
val freeze : unit -> t
val restore : t -> unit
