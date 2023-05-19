open Types

module MapImpl = Map.Make(FreeRowID)

type t = mono_row MapImpl.t

let current_map = ref MapImpl.empty

let add (id : FreeRowID.t) (row : mono_row) : unit =
  current_map := MapImpl.add id row !current_map

let find_opt (id : FreeRowID.t) : mono_row option =
  MapImpl.find_opt id !current_map

let freeze () : t =
  !current_map

let restore (map : t) : unit =
  current_map := map
