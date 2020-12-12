
module Variant : sig
  type t
  [@@deriving show]

  val initialize : unit -> unit

  val fresh : string -> t

  val extract_name : t -> string

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val show_direct : t -> string
end

module Synonym : sig
  type t
  [@@deriving show]

  val initialize : unit -> unit

  val fresh : string -> t

  val extract_name : t -> string

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val show_direct : t -> string
end

module Opaque : sig
  type t
  [@@deriving show]

  val initialize : unit -> unit

  val fresh : string -> t

  val extract_name : t -> string

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val show_direct : t -> string
end

type t =
  | Variant of Variant.t
  | Synonym of Synonym.t
  | Opaque  of Opaque.t
[@@deriving show]
