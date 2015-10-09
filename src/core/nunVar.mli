
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Variable} *)

type id = NunID.t

type 'ty t = private {
  id: id;
  ty: 'ty;
}

val equal : 'a t -> 'a t -> bool
(** Equality, purely by identifier. It is impossible to forge two variables
    with the same identifier but distinct types *)

val compare : 'a t -> 'a t -> int
(** Total order based on {!id} *)

val make : ty:'ty -> name:string -> 'ty t
(** [make ~ty ~name] makes a new variable with the given name and type. It
    will have a unique identifier *)

val fresh_copy : 'ty t -> 'ty t
(** [fresh_copy v] makes a variable that looks like [v] but has a fresh
    identifier *)

val of_id : ty:'ty -> id -> 'ty t
(** [of_id ~ty id] makes a variable with the given ID *)

val ty : 'ty t -> 'ty

val id : _ t -> id

val update_ty : 'a t -> f:('a -> 'b) -> 'b t
(** Update the type, and make a new variable with it with {b THE SAME ID}.
    Careful not to break invariants. *)

val fresh_update_ty : 'a t -> f:('a -> 'b) -> 'b t
(** Update the type, and make a new variable with it with a fresh ID. *)

val print : Format.formatter -> _ t -> unit
val to_string : _ t -> string

(** {2 Substitutions} *)

module type SUBST = sig
  type ty
  type var = ty t

  type 'a t
  (** A substitution for those variables *)

  val empty : 'a t
  val is_empty : _ t -> bool

  val add : subst:'a t -> var -> 'a -> 'a t

  val mem : subst:'a t -> var -> bool
  val find : subst:'a t -> var -> 'a option
  val find_exn : subst:'a t -> var -> 'a  (** @raise Not_found if var not bound *)

  val to_list : 'a t -> (var * 'a) list
end

module Subst(Ty : sig type t end) : SUBST with type ty = Ty.t
