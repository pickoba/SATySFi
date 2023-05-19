open Types

module MapImpl = Map.Make(FreeID)

type t = mono_type MapImpl.t

let current_map = ref MapImpl.empty

let add (id : FreeID.t) (ty : mono_type) : unit =
  current_map := MapImpl.add id ty !current_map

let find_opt (id : FreeID.t) : mono_type option =
  MapImpl.find_opt id !current_map

let freeze () : t =
  !current_map

let restore (map : t) : unit =
  current_map := map
