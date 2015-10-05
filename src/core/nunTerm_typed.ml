
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

module TyI = NunType_intf

module Loc = NunLocation
module Var = NunVar
module MetaVar = NunMetaVar
module ID = NunID

(*$inject
  module Var = NunVar

*)

type loc = Loc.t
type id = NunID.t
type 'a var = 'a Var.t

type ('a, 'ty, 'kind) view =
  | Builtin : NunBuiltin.T.t -> ('a, 'ty, [>]) view (** built-in symbol *)
  | Const : id -> ('a, 'ty, [>]) view (** top-level symbol *)
  | Var : 'ty var -> ('a, 'ty, [>]) view (** bound variable *)
  | App : 'a * 'a list -> ('a, 'ty, [>]) view
  | Fun : 'ty var * 'a -> ('a, 'ty, [>]) view
  | Forall : 'ty var * 'a -> ('a, 'ty, [>]) view
  | Exists : 'ty var * 'a -> ('a, 'ty, [>]) view
  | Let : 'ty var * 'a * 'a -> ('a, 'ty, [>]) view
  | TyKind : ('a, 'ty, [>]) view
  | TyType : ('a, 'ty, [>]) view
  | TyMeta : 'ty NunMetaVar.t -> ('a, 'ty, [>`Meta]) view
  | TyBuiltin : NunBuiltin.Ty.t -> ('a, 'ty, [>]) view (** Builtin type *)
  | TyArrow : 'ty * 'ty -> ('a, 'ty, [>]) view   (** Arrow type *)
  | TyForall : 'ty var * 'ty -> ('a, 'ty, [>`Poly]) view  (** Polymorphic/dependent type *)

(** {2 Read-Only View} *)
module type VIEW = sig
  type t

  type kind
  type ty = private t

  val view : t -> (t, ty, kind) view

  val ty : t -> ty option
  (** The type of a term *)
end

(** {2 Full Signature} *)
module type S = sig
  include VIEW

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t and type t = ty
    include NunIntf.PRINT with type t := t
  end

  val loc : t -> loc option

  val ty : t -> Ty.t option
  (** Type of this term *)

  val const : ?loc:loc -> ty:Ty.t -> id -> t
  val builtin : ?loc:loc -> ty:Ty.t -> NunBuiltin.T.t -> t
  val var : ?loc:loc -> Ty.t var -> t
  val app : ?loc:loc -> ty:Ty.t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:Ty.t -> ty var -> t -> t
  val let_ : ?loc:loc -> ty var -> t -> t -> t
  val forall : ?loc:loc -> ty var -> t -> t
  val exists : ?loc:loc -> ty var -> t -> t

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

type 'a printer = Format.formatter -> 'a -> unit

module type PRINT = sig
  type term

  val print : term printer
  val print_in_app : term printer
  val print_in_binder : term printer
end

module Print(T : VIEW) = struct
  type term = T.t

  let fpf = Format.fprintf

  let rec print out ty = match T.view ty with
    | TyKind -> CCFormat.string out "kind"
    | TyType -> CCFormat.string out "type"
    | Builtin b -> CCFormat.string out (NunBuiltin.T.to_string b)
    | TyBuiltin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
    | Const id -> ID.print out id
    | TyMeta v -> ID.print out (MetaVar.id v)
    | Var v -> Var.print out v
    | App (f, [a;b]) ->
        begin match T.view f with
        | Builtin s when NunBuiltin.T.fixity s = `Infix ->
            fpf out "@[<hov>%a@ %s@ %a@]"
              print_in_app a (NunBuiltin.T.to_string s) print_in_app b
        | _ ->
            fpf out "@[<hov2>%a@ %a@ %a@]" print_in_app f
              print_in_app a print_in_app b
        end
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | Let (v,t,u) ->
        fpf out "@[<2>let %a :=@ %a in@ %a@]" Var.print v print t print u
    | Fun (v, t) ->
        fpf out "@[<2>fun %a:%a.@ %a@]" Var.print v print_ty_in_app (Var.ty v) print t
    | Forall (v, t) ->
        fpf out "@[<2>forall %a:%a.@ %a@]" Var.print v print_ty_in_app (Var.ty v) print t
    | Exists (v, t) ->
        fpf out "@[<2>forall %a:%a.@ %a@]" Var.print v print_ty_in_app (Var.ty v) print t
    | TyArrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_ty_in_arrow a print_ty b
    | TyForall (v,t) ->
        fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print_ty t

  and print_ty out ty = print out (ty:T.ty:>T.t)
  and print_ty_in_app out ty = print_in_app out (ty:T.ty:>T.t)
  and print_ty_in_arrow out ty = print_in_binder out (ty:T.ty:>T.t)

  and print_in_app out t = match T.view t with
    | Builtin _ | TyBuiltin _ | TyKind | TyType
    | Var _ | Const _ | TyMeta _ ->
        print out t
    | App (_,_)
    | Forall _
    | Exists _
    | Fun _
    | Let _
    | TyArrow (_,_)
    | TyForall (_,_) -> fpf out "@[(%a)@]" print t

  and print_in_binder out t = match T.view t with
    | Builtin _ | TyBuiltin _ | TyKind | TyType | Var _
    | Const _ | TyMeta _ | App (_,_) ->
        print out t
    | Forall _
    | Exists _
    | Fun _
    | Let _
    | TyArrow (_,_)
    | TyForall (_,_) -> fpf out "@[(%a)@]" print t
end

(** {2 Default Instance} *)
module Default = struct
  type t = {
    view : (t,t) view;
    loc : Loc.t option;
    mutable ty : t option;
  }

  type ty = t

  (* dereference the term, if it is a variable, until it is not bound *)
  let rec deref_rec_ t = match t.view with
    | TyMeta var ->
        begin match MetaVar.deref var with
        | None -> t
        | Some t' ->
            let root = deref_rec_ t' in
            (* path compression *)
            if t' != root then MetaVar.rebind ~var root;
            root
        end
    | _ -> t

  let view t = (deref_rec_ t).view

  let loc t = t.loc

  let ty t = t.ty

  (* special constants: kind and type *)
  let kind_ = {view=TyKind; loc=None; ty=None}
  let type_ = {view=TyType; loc=None; ty=Some kind_}
  let prop = {view=TyBuiltin NunBuiltin.Ty.Prop; loc=None; ty=Some type_}

  let make_raw_ ~loc ~ty view = { view; loc; ty}

  let make_ ?loc ?ty view = match view with
    | App ({view=App (f, l1); loc; _}, l2) ->
        make_raw_ ~loc ~ty (App (f, l1 @ l2))
    | _ -> make_raw_ ~loc ~ty view

  let builtin ?loc ~ty s = make_ ?loc ~ty (Builtin s)
  let const ?loc ~ty id = make_ ?loc ~ty (Const id)
  let var ?loc v = make_ ?loc ~ty:(Var.ty v) (Var v)
  let app ?loc ~ty t l =
    if l=[] then t else make_ ?loc ~ty (App (t, l))
  let fun_ ?loc ~ty v t = make_ ?loc ~ty (Fun (v, t))
  let let_ ?loc v t u = make_ ?loc ?ty:u.ty (Let (v, t, u))
  let forall ?loc v t = make_ ?loc ~ty:prop (Forall (v, t))
  let exists ?loc v t = make_ ?loc ~ty:prop (Exists (v, t))

  let ty_type = type_
  let ty_prop = prop

  let ty_builtin ?loc b = make_ ?loc ~ty:type_ (TyBuiltin b)
  let ty_const ?loc id = const ?loc ~ty:type_ id
  let ty_var ?loc v = var ?loc v
  let ty_meta_var ?loc v = make_ ?loc (TyMeta v)
  let ty_app ?loc f l =
    if l=[] then f else app ?loc ~ty:type_ f l
  let ty_arrow ?loc a b = make_ ?loc ~ty:type_ (TyArrow (a,b))
  let ty_forall ?loc a b = make_ ?loc ~ty:type_ (TyForall(a,b))

  module Ty = struct
    type term = t

    type t = term

    let is_Type t = match (deref_rec_ t).view with
      | TyType -> true
      | _ -> false

    let is_Kind t = match (deref_rec_ t).view with
      | TyKind -> true
      | _ -> false

    let rec returns_Type t = match (deref_rec_ t).view with
      | TyType -> true
      | TyArrow (_, t')
      | TyForall (_, t') -> returns_Type t'
      | _ -> false

    let to_term t = t

    let is_ty t = match t.ty with
      | Some ty -> is_Type ty
      | _ -> false

    let of_term t =
      if is_ty t then Some t else None

    let of_term_exn t =
      if is_ty t then t else failwith "Term_mut.TyI.of_term_exn"

    let view t = match (deref_rec_ t).view with
      | TyKind -> TyI.Kind
      | TyType -> TyI.Type
      | TyBuiltin b -> TyI.Builtin b
      | TyMeta v -> TyI.Meta v
      | Const id -> TyI.Const id
      | Var v -> TyI.Var v
      | App (f,l) -> TyI.App (f,l)
      | TyArrow (a,b) -> TyI.Arrow (a,b)
      | TyForall (v,t) -> TyI.Forall (v,t)
      | Builtin _
      | Fun _
      | Forall _
      | Exists _
      | Let _ -> assert false

    include TyI.Print(struct type t = ty let view = view end)
  end

  include Print(struct
    type ty = t
    type t = ty

    let view = view
    let ty = ty
  end)
end

module AsHO(T : VIEW)
  : NunTerm_ho.VIEW
  with type t = T.t and type ty = T.ty
= struct

  module TI = NunTerm_ho

  type t = T.t
  type ty = T.ty

  let view t = match T.view t with
    | Builtin b -> TI.Builtin b
    | Const id -> TI.Const id
    | Var v -> TI.Var v
    | App (f,l) -> TI.App (f, l)
    | Fun (v,t) -> TI.Fun (v, t)
    | Forall (v,t) -> TI.Forall (v,t)
    | Exists (v,t) -> TI.Exists (v,t)
    | Let (v,t,u) -> TI.Let (v,t,u)
    | TyKind -> TI.TyKind
    | TyType -> TI.TyType
    | TyMeta _ -> failwith "Term_typed.AsHO.view: remaining meta"
    | TyBuiltin b -> TI.TyBuiltin b
    | TyArrow (a,b) -> TI.TyArrow (a,b)
    | TyForall (v,t) -> TI.TyForall (v,t)

end
