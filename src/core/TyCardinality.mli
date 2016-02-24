
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Compute the cardinality of Types} *)

module TI = TermInner

exception Error of string

exception Polymorphic

(** Approximation of a cardinal, including infinite cardinals *)
module Card : sig
  type t =
    | Bounded of Z.t
    | Unknown
    | Infinite

  val (+) : t -> t -> t
  val ( * ) : t -> t -> t
  val zero : t
  val one : t
  val of_int : int -> t
  val of_z : Z.t -> t

  val infinite : t
  val unknown : t

  include Intf.EQ with type t := t
  include Intf.HASH with type t := t
  val print : t CCFormat.printer
end

module Make(T : TI.S) : sig
  type ty = T.t

  type ('a, 'inv) env = ('a, ty, 'inv) Env.t constraint 'inv = <ty:[`Mono]; ..>
  (** We only consider monomorphic types *)

  val cardinality_ty_id : (_, _) env -> ID.t -> Card.t
  (** [cardinality id] computes the cardinality of the type
      named [id].
      @raise Error if [id] is not a valid type in [env]
      @raise Polymorphic if the type is polymorphic,
        or depends on polymorphic types *)

  val cardinality_ty : (_, _) env -> ty -> Card.t
  (** Same as {!cardinality_ty_id} but takes a type as argument. The
      type must be a symbol or the application of a symbol to arguments.
      @raise Error if [id] is not a valid type in [env]
      @raise Polymorphic if the type is polymorphic,
        or depends on polymorphic types *)

end
