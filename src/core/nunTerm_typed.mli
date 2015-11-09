
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t

type ('a,'inv) view = ('a,'inv) NunTerm_intf.view

(** {2 Read-Only View} *)
module type VIEW = sig
  type invariant =
    <meta:NunMark.with_meta; poly: NunMark.polymorph>

  type t
  type ty = t
  val view : t -> (t, invariant) view

  val ty : t -> ty option
  (** The type of a term *)

  module Ty : sig
    type ty = t
    val view : t -> (t,invariant) NunType_intf.view
  end
end

(** {2 Full Signature} *)
module type S = sig
  type invariant =
    <meta:NunMark.with_meta; poly: NunMark.polymorph>

  type t
  type ty = t

  val view : t -> (t, invariant) view

  val ty : t -> ty option
  (** The type of a term *)

  module Ty : sig
    include NunType_intf.AS_TERM
      with type term = t and type t = ty
      and type invariant_poly = NunMark.polymorph
      and type invariant_meta = NunMark.with_meta
    include NunIntf.PRINT with type t := t
    type ty = t

    val is_ty : term -> bool (** [is_ty t] same as [is_Type (type of t)] *)
  end

  val loc : t -> loc option

  val const : ?loc:loc -> ty:Ty.t -> id -> t
  val builtin : ?loc:loc -> ty:Ty.t -> NunBuiltin.T.t -> t
  val app_builtin : ?loc:loc -> ty:Ty.t -> NunBuiltin.T.t -> t list -> t
  val var : ?loc:loc -> Ty.t var -> t
  val app : ?loc:loc -> ty:Ty.t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:Ty.t -> ty var -> t -> t
  val let_ : ?loc:loc -> ty var -> t -> t -> t
  val match_with : ?loc:loc -> ty:Ty.t -> t -> ty NunTerm_intf.cases -> t
  val ite : ?loc:loc -> t -> t -> t -> t
  val forall : ?loc:loc -> ty var -> t -> t
  val exists : ?loc:loc -> ty var -> t -> t
  val eq : ?loc:loc -> t -> t -> t

  val mk_bind :
    ?loc:loc ->
    ty:Ty.t ->
    NunMark.polymorph NunTerm_intf.binder ->
    Ty.t var ->
    t ->
    t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunBuiltin.Ty.t -> Ty.t
  val ty_const : ?loc:loc -> id -> Ty.t
  val ty_var : ?loc:loc -> ty var -> Ty.t
  val ty_meta_var : ?loc:loc -> Ty.t NunMetaVar.t -> Ty.t  (** Meta-variable, ready for unif *)
  val ty_app : ?loc:loc -> Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ?loc:loc -> ty var -> Ty.t -> Ty.t
  val ty_arrow : ?loc:loc -> Ty.t -> Ty.t -> Ty.t
end

(** {2 Default Instance} *)

module Default : sig
  include S

  include NunTerm_ho.PRINT with type term = t and type ty := ty
end

val default : (module S with type t = Default.t)

(** {2 View as {!NunTerm_ho.VIEW}}

  Typed terms can be considered as regular higher-order terms, but
  only for reading — writing requires providing the type at every
  application *)

module AsHO(T : VIEW) :
  NunTerm_ho.VIEW
    with type invariant_poly = NunMark.polymorph
    and type invariant_meta = NunMark.without_meta
    and type t = T.t and type ty = T.t

val as_ho : (module NunTerm_ho.VIEW with type t = Default.t
  and type invariant_meta=NunMark.without_meta
  and type invariant_poly=NunMark.polymorph)
