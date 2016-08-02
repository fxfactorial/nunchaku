
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Main View for terms} *)

module ID = ID
module Var = Var
module MetaVar = MetaVar

type id = ID.t
type 'a var = 'a Var.t
type 'a or_error = ('a, string) CCResult.t
type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf

let print_undefined_id : bool ref = ref false
(** global option affecting printing: if true, undefined values will
    be displayed as "undefined_42" rather than "?__" *)

(* precedence. Order matters, as it defines priorities *)
type prec =
  | P_bot
  | P_app
  | P_arrow
  | P_eq
  | P_not
  | P_guard
  | P_ite
  | P_bind
  | P_and
  | P_or
  | P_top (* toplevel precedence *)

module Binder = struct
  type t =
    [ `Forall
    | `Exists
    | `Fun
    | `TyForall
    | `Mu  (** fixpoint *)
    ]

  let to_string : t -> string = function
    | `Fun -> "fun"
    | `Forall -> "forall"
    | `Exists -> "exists"
    | `TyForall -> "pi"
    | `Mu -> "mu"
end

module TyBuiltin = struct
  type t =
    [ `Kind
    | `Type
    | `Prop
    | `Unitype (** when there is only one type *)
    ]
  let equal = (=)
  let compare = Pervasives.compare
  let to_string = function
    | `Prop -> "prop"
    | `Kind -> "kind"
    | `Type -> "type"
    | `Unitype -> "unitype"
end

module Builtin = struct
  type +'a guard = {
    assuming: 'a list; (* preconditions *)
    asserting: 'a list; (* postconditions, to be enforced *)
  }

  let empty_guard = {asserting=[]; assuming=[]}

  let map_guard f g =
    { assuming = List.map f g.assuming;
      asserting = List.map f g.asserting;
    }

  let merge_guard g1 g2 =
    { assuming = List.rev_append g1.assuming g2.assuming;
      asserting = List.rev_append g1.asserting g2.asserting;
    }

  type 'a t =
    [ `True
    | `False
    | `Not of 'a
    | `Or of 'a list
    | `And of 'a list
    | `Imply of 'a * 'a
    | `Ite of 'a * 'a * 'a
    | `Eq of 'a * 'a
    | `DataTest of id (** Test whether [t : tau] starts with given constructor *)
    | `DataSelect of id * int (** Select n-th argument of given constructor *)
    | `Undefined_self of id * 'a (** Undefined case. argument=the undefined term *)
    | `Undefined_atom of id * 'a (** Undefined term (name+type) *)
    | `Unparsable of 'a (** could not parse model properly. Param=ty *)
    | `Guard of 'a * 'a guard (** term + some boolean conditions *)
    ]

  let prec : _ t -> prec = function
    | `True
    | `False
    | `DataSelect _
    | `DataTest _
    | `Undefined_atom _ -> P_bot
    | `Eq _ -> P_eq
    | `Not _ -> P_not
    | `Imply _
    | `Or _ -> P_or
    | `And _ -> P_and
    | `Guard _ -> P_guard
    | `Undefined_self _ -> P_app
    | _ -> P_top

  let rec print_infix_list pterm s out l = match l with
    | [] -> assert false
    | [t] -> pterm out t
    | t :: l' ->
        fpf out "@[%a@]@ %s %a"
          pterm t s (print_infix_list pterm s) l'

  let pp pterm out : _ t -> unit = function
    | `True -> CCFormat.string out "true"
    | `False -> CCFormat.string out "false"
    | `Not x -> fpf out "@[<2>~@ %a@]" pterm x
    | `Or l ->
        fpf out "@[<hv>%a@]" (print_infix_list pterm "||") l
    | `And l ->
        fpf out "@[<hv>%a@]" (print_infix_list pterm "&&") l
    | `Imply (a,b) -> fpf out "@[@[%a@]@ @[<2>=>@ @[%a@]@]@]" pterm a pterm b
    | `Eq (a,b) ->
        fpf out "@[<hv>%a@ @[<hv>=@ %a@]@]" pterm a pterm b
    | `Ite (a,b,c) ->
        fpf out "@[<hv>@[<2>if@ %a@]@ @[<2>then@ %a@]@ @[<2>else@ %a@]@]"
          pterm a pterm b pterm c
    | `DataTest id -> fpf out "is-%s" (ID.name id)
    | `DataSelect (id, n) ->
        fpf out "select-%s-%d" (ID.name id) n
    | `Undefined_self (id,t) ->
        if !print_undefined_id
        then fpf out "undefined_%d %a" (ID.id id) pterm t
        else fpf out "?__ %a" pterm t
    | `Undefined_atom (id,_ty) ->
        if !print_undefined_id
        then fpf out "undefined_%d" (ID.id id)
        else CCFormat.string out "?__"
    | `Unparsable ty -> fpf out "@[<2>?__unparsable@ @[%a@]@]" pterm ty
    | `Guard (t, o) ->
        let pp_case name out l = match l with
          | [] -> ()
          | _::_ ->
              fpf out "@ @[<2>%s@ @[<hv>%a@]@]" name
                (CCFormat.list ~start:"" ~stop:"" ~sep:" && " pterm) l
        in
        assert (not (o.asserting=[] && o.assuming=[]));
        fpf out "@[<hv>%a%a%a@]" pterm t
          (pp_case "assuming") o.assuming
          (pp_case "asserting") o.asserting

  let equal
  : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  = fun eqterm a b -> match a, b with
    | `True, `True
    | `False, `False -> true
    | `Not a, `Not b -> eqterm a b
    | `Imply (a1,b1), `Imply (a2,b2) -> eqterm a1 a2 && eqterm b1 b2
    | `Or l1, `Or l2 -> CCList.equal eqterm l1 l2
    | `And l1, `And l2 -> CCList.equal eqterm l1 l2
    | `Ite(a1,b1,c1), `Ite(a2,b2,c2) ->
        eqterm a1 a2 && eqterm b1 b2 && eqterm c1 c2
    | `Eq(a1,b1), `Eq (a2,b2) -> eqterm a1 a2 && eqterm b1 b2
    | `DataTest id, `DataTest id' -> ID.equal id id'
    | `DataSelect (id, n), `DataSelect (id', n') -> n=n' && ID.equal id id'
    | `Undefined_self (a,t1), `Undefined_self (b,t2) -> ID.equal a b && eqterm t1 t2
    | `Undefined_atom (a,t1), `Undefined_atom (b,t2) -> ID.equal a b && eqterm t1 t2
    | `Unparsable t1, `Unparsable t2 -> eqterm t1 t2
    | `Guard (t1, g1), `Guard (t2, g2) ->
        List.length g1.assuming = List.length g2.assuming
        && List.length g1.asserting = List.length g2.asserting
        && eqterm t1 t2
        && List.for_all2 eqterm g1.assuming g2.assuming
        && List.for_all2 eqterm g1.asserting g2.asserting
    | `Guard _, _
    | `True, _ | `False, _ | `Ite _, _ | `Not _, _ | `Unparsable _, _
    | `Eq _, _ | `Or _, _ | `And _, _ | `Imply _, _
    | `DataSelect _, _ | `DataTest _, _
    | `Undefined_self _, _ | `Undefined_atom _, _ -> false

  let map : f:('a -> 'b) -> 'a t -> 'b t
  = fun ~f b -> match b with
    | `True -> `True
    | `False -> `False
    | `And l -> `And (List.map f l)
    | `Imply (a,b) -> `Imply (f a, f b)
    | `Ite (a,b,c) -> `Ite (f a, f b, f c)
    | `Eq (a,b) -> `Eq (f a, f b)
    | `DataTest id -> `DataTest id
    | `Or l -> `Or (List.map f l)
    | `Not t -> `Not (f t)
    | `DataSelect (c,n) -> `DataSelect (c,n)
    | `Undefined_self (id, t) -> `Undefined_self (id, f t)
    | `Undefined_atom (id, t) -> `Undefined_atom (id, f t)
    | `Unparsable t -> `Unparsable (f t)
    | `Guard (t, g) ->
        let g' = map_guard f g in
        `Guard (f t, g')

  let fold : f:('acc -> 'a -> 'acc) -> x:'acc -> 'a t -> 'acc
  = fun ~f ~x:acc b -> match b with
    | `True
    | `False
    | `DataTest _
    | `DataSelect _ -> acc
    | `Imply (a,b) -> f (f acc a) b
    | `Not t -> f acc t
    | `Or l
    | `And l -> List.fold_left f acc l
    | `Ite (a,b,c) -> f (f (f acc a) b) c
    | `Eq (a,b) -> f (f acc a) b
    | `Unparsable t
    | `Undefined_atom (_,t)
    | `Undefined_self (_,t) -> f acc t
    | `Guard (t, g) ->
        let acc = f acc t in
        let acc = List.fold_left f acc g.assuming in
        List.fold_left f acc g.asserting

  let fold2_l ~f ~fail ~x l1 l2 =
    if List.length l1=List.length l2
    then List.fold_left2 f x l1 l2
    else fail ()

  let fold2 :
      f:('acc -> 'a -> 'b -> 'acc) -> fail:(unit -> 'acc) ->
        x:'acc -> 'a t -> 'b t -> 'acc
  = fun ~f ~fail ~x:acc b1 b2 -> match b1, b2 with
    | `True, `True
    | `False, `False -> acc
    | `Imply (a1,b1), `Imply (a2,b2) ->
        let acc = f acc a1 a2 in f acc b1 b2
    | `Not a, `Not b -> f acc a b
    | `And l1, `And l2 -> fold2_l ~f ~fail ~x:acc l1 l2
    | `Or l1, `Or l2 -> fold2_l ~f ~fail ~x:acc l1 l2
    | `DataTest i1, `DataTest i2 -> if ID.equal i1 i2 then acc else fail()
    | `DataSelect (i1,n1), `DataSelect (i2,n2) ->
        if n1=n2 && ID.equal i1 i2 then acc else fail()
    | `Ite (a1,b1,c1), `Ite(a2,b2,c2) ->
        let acc = f acc a1 a2 in
        let acc = f acc b1 b2 in
        f acc c1 c2
    | `Eq (a1,b1), `Eq (a2,b2) -> let acc = f acc a1 a2 in f acc b1 b2
    | `Undefined_self (i1,t1), `Undefined_self (i2,t2)
    | `Undefined_atom (i1,t1), `Undefined_atom (i2,t2) ->
        if ID.equal i1 i2 then f acc t1 t2 else fail()
    | `Unparsable t1, `Unparsable t2 -> f acc t1 t2
    | `Guard (t1, g1), `Guard (t2, g2)
      when List.length g1.asserting=List.length g2.asserting
      && List.length g1.assuming = List.length g2.assuming ->
        let acc = f acc t1 t2 in
        let acc = List.fold_left2 f acc g1.assuming g2.assuming in
        List.fold_left2 f acc g1.asserting g2.asserting
    | `Guard _, _
    | `True, _ | `False, _ | `Ite _, _ | `Not _, _ | `Unparsable _, _
    | `Eq _, _ | `Or _, _ | `And _, _ | `Imply _, _
    | `DataSelect _, _ | `DataTest _, _
    | `Undefined_self _, _ | `Undefined_atom _, _ -> fail()

  let iter : ('a -> unit) -> 'a t -> unit
  = fun f b -> match b with
    | `True
    | `False
    | `DataTest _
    | `DataSelect _ -> ()
    | `Imply (a,b) -> f a; f b
    | `Not t -> f t
    | `And l
    | `Or l -> List.iter f l
    | `Ite (a,b,c) -> f a; f b; f c
    | `Eq (a,b) -> f a; f b
    | `Unparsable t
    | `Undefined_atom (_,t)
    | `Undefined_self (_,t) -> f t
    | `Guard (t,g) ->
        f t;
        List.iter f g.asserting;
        List.iter f g.assuming

  let to_seq b f = iter f b

  let to_sexp
  : ('a -> CCSexp.t) -> 'a t -> CCSexp.t
  = fun cterm t ->
    let str = CCSexp.atom and lst = CCSexp.of_list in
    match t with
      | `True -> str "true"
      | `False -> str "false"
      | `Not x -> lst [str "not"; cterm x]
      | `Or l -> lst (str "or" :: List.map cterm l)
      | `And l -> lst (str "and" :: List.map cterm l)
      | `Imply (a,b) -> lst [str "imply"; cterm a; cterm b]
      | `Eq (a,b) -> lst [str "="; cterm a; cterm b]
      | `Ite (a,b,c) -> lst [str "if"; cterm a; cterm b; cterm c]
      | `DataTest id -> str ("is-" ^ ID.to_string id)
      | `DataSelect (id, n) ->
        str (CCFormat.sprintf "select-%s-%d" (ID.name id) n)
      | `Undefined_self (id,t) ->
        lst [str "?__"; str (ID.to_string id); cterm t]
      | `Undefined_atom _ -> str "?__"
      | `Unparsable ty ->
        lst [str "?__unparsable"; cterm ty]
      | `Guard _ -> assert false (* TODO *)
end

type 'a case = 'a var list * 'a
(** A pattern match case for a given constructor [ vars, right-hand side ]
    The pattern must be linear (variable list does not contain duplicates) *)

(** A list of cases (indexed by constructor) *)
type 'a cases = 'a case ID.Map.t

let cases_to_list = ID.Map.to_list

(* check that: each case is linear (all vars are different) *)
let cases_well_formed (type a) m =
  let is_linear_ _ (vars,_) =
    let module VarSet = Var.Set(struct type t = a end) in
    VarSet.cardinal (VarSet.of_list vars) = List.length vars
  in
  ID.Map.for_all is_linear_ m

(** The main view of terms. Other representations will be refinements
  (read: restrictions) of this view that enforce additional restrictions, such
  as the absence of meta-variables or polymorphism *)
type 'a view =
  | Const of id (** top-level symbol *)
  | Var of 'a var (** bound variable *)
  | App of 'a * 'a list
  | Builtin of 'a Builtin.t (** built-in operation *)
  | Bind of Binder.t * 'a var * 'a
  | Let of 'a var * 'a * 'a
  | Match of 'a * 'a cases (** shallow pattern-match *)
  | TyBuiltin of TyBuiltin.t (** Builtin type *)
  | TyArrow of 'a * 'a  (** Arrow type *)
  | TyMeta of 'a MetaVar.t

(* NOTE: Eq has its own case (in Builtin), because its type parameter is often hidden.
   For instance, when we parse a model back from TPTP or SMT, equalities
   are not annotated with their type parameter; we would have to compute or
   infer types again for an unclear benefit (usually just for printing).

   Instead, we just consider equality  to be a specific "ad-hoc polymorphic"
   predicate and do not require it to have a type argument.
 *)

type 't repr = 't -> 't view
(** A concrete representation of terms by the type [t'] *)

type 't build = 't view -> 't
(** A builder for a concrete representation with type ['t]. *)

module type REPR = sig
  type t
  val repr : t repr
end

module type BUILD = sig
  type t
  val build : t build
end

module type S = sig
  type t
  include REPR with type t := t
  include BUILD with type t := t
end

(** {2 Printing} *)

module type PRINT = sig
  type t
  val print : t printer
  val print' : prec -> t printer
  val print_in_app : t printer
  val print_in_binder : t printer
  val to_string : t -> string

  val to_sexp : t -> CCSexp.t
end

module Print(T : REPR)
: PRINT with type t = T.t
= struct
  type t = T.t

  let pp_list_ ?(start="") ?(stop="") ~sep pp =
    CCFormat.list ~start ~stop ~sep pp

  let is_if_ t = match T.repr t with
    | Builtin (`Ite _) -> true
    | _ -> false

  let rec unroll_if_ t = match T.repr t with
    | Builtin (`Ite (a,b,c)) ->
        let l, last = unroll_if_ c in
        (a,b) :: l, last
    | _ -> [], t

  let rec unroll_binder b t = match T.repr t with
    | Bind (b', v, t') when b=b' ->
        let vars, body = unroll_binder b t' in
        v :: vars, body
    | _ -> [], t

  let right_assoc_ = function
    | P_eq
    | P_guard
    | P_app
    | P_and
    | P_or -> false
    | P_bot
    | P_top
    | P_not
    | P_arrow
    | P_ite
    | P_bind -> true

  (* put "()" around [fmt] if needed *)
  let wrap p1 p2 out fmt =
    if p1>p2 || (p1 = p2 && (not (right_assoc_ p1)))
    then (
      CCFormat.string out "(";
      Format.kfprintf (fun _ -> CCFormat.string out ")") out fmt
    )
    else Format.kfprintf (fun _ -> ()) out fmt

  let rec print' p out t = match T.repr t with
    | TyBuiltin b -> CCFormat.string out (TyBuiltin.to_string b)
    | Const id -> ID.print out id
    | TyMeta v -> MetaVar.print out v
    | Var v -> Var.print_full out v
    | Builtin (`Ite (a,b,c)) when is_if_ c ->
        (* special case to avoid deep nesting of ifs *)
        let pp_middle out (a,b) =
          fpf out "@[<2>else if@ @[%a@]@]@ @[<2>then@ @[%a@]@]"
            (print' P_ite) a (print' P_ite) b
        in
        let middle, last = unroll_if_ c in
        assert (not (is_if_ last));
        wrap P_ite p out
          "@[<hv>@[<2>if@ @[%a@]@]@ @[<2>then@ %a@]@ %a@ @[<2>else@ %a@]@]"
          (print' P_ite) a (print' P_ite) b
          (pp_list_ ~sep:"" pp_middle) middle
          (print' P_ite) last
    | Builtin b ->
        let p' = Builtin.prec b in
        wrap p' p out "%a" (Builtin.pp (print' p')) b
    | App (f,l) ->
        wrap P_app p out "@[<2>%a@ %a@]" print_in_app f
          (pp_list_ ~sep:" " print_in_app) l
    | Let (v,t,u) ->
        wrap P_top p out "@[<2>let %a :=@ %a in@ %a@]" Var.print_full v print t print u
    | Match (t,l) ->
        let pp_case out (id,(vars,t)) =
          fpf out "@[<hv2>| @[<hv2>%a %a@] ->@ %a@]"
            ID.print id (pp_list_ ~sep:" " Var.print_full) vars print t
        in
        fpf out "@[<hv>@[<hv2>match @[%a@] with@ %a@]@ end@]"
          print t (pp_list_ ~sep:"" pp_case) (ID.Map.to_list l)
    | Bind (b, _, _) ->
        let s = Binder.to_string b in
        let vars, body = unroll_binder b t in
        wrap P_bind p out "@[<2>%s @[<hv>%a@].@ %a@]" s
          (pp_list_ ~sep:" " pp_typed_var) vars print_in_binder body
    | TyArrow (a,b) ->
        wrap P_arrow p out "@[<2>%a ->@ %a@]" (print' P_arrow) a (print' P_arrow) b
  and pp_typed_var out v =
    let ty = Var.ty v in
    fpf out "(@[%a:@,@[%a@]@])" Var.print_full v print ty
  and print_in_app out t = print' P_app out t
  and print_in_binder out t = print' P_bind out t
  and print out t = print' P_top out t

  let to_string = CCFormat.to_string print

  let str = CCSexp.atom
  let lst = CCSexp.of_list

  let rec to_sexp t : CCSexp.t = match T.repr t with
    | TyBuiltin b -> str (TyBuiltin.to_string b)
    | Const id -> str (ID.to_string id)
    | TyMeta _ -> assert false
    | Var v -> str (Var.to_string_full v)
    | Builtin b -> Builtin.to_sexp to_sexp b
    | App (f,l) -> lst (to_sexp f :: List.map to_sexp l)
    | Let (v,t,u) ->
      lst [str "let"; lst [lst [var_to_sexp v; to_sexp t]]; to_sexp u]
    | Match (t,l) ->
      lst
        (str "match" ::
           to_sexp t ::
           ID.Map.fold
             (fun c (vars,t) acc ->
                lst [str (ID.to_string c); lst (List.map var_to_sexp vars); to_sexp t]
                :: acc)
             l [])
    | Bind (b, _, _) ->
      let s = Binder.to_string b in
      let vars, body = unroll_binder b t in
      lst [str s; lst (List.map var_to_sexp vars); to_sexp body]
    | TyArrow (a,b) ->
      lst [str "->"; to_sexp a; to_sexp b]
  and var_to_sexp v =
    lst [str (Var.to_string_full v); to_sexp (Var.ty v)]
end

type 'a print = (module PRINT with type t = 'a)

(** {2 Utils} *)

module type UTIL_REPR = sig
  type t_

  val head_sym : t_ -> id
  (** Search for a head symbol
      @raise Not_found if not an application/const *)

  val to_seq : t_ -> t_ Sequence.t
  (** Iterate on sub-terms *)

  val to_seq_vars : t_ -> t_ Var.t Sequence.t
  (** Iterate on variables *)

  val to_seq_consts : t_ -> ID.t Sequence.t
  (** IDs occurring as {!Const} *)

  module VarSet : CCSet.S with type elt = t_ Var.t

  val to_seq_free_vars : ?bound:VarSet.t -> t_ -> t_ Var.t Sequence.t
  (** Iterate on free variables. *)

  val free_vars : ?bound:VarSet.t -> t_ -> VarSet.t
  (** [free_vars t] computes the set of free variables of [t].
      @param bound variables bound on the path *)

  val is_var : t_ -> bool
  val is_const : t_ -> bool

  val is_closed : t_ -> bool
  (** [is_closed t] means [to_seq_free_vars t = empty] *)

  val is_undefined : t_ -> bool

  val free_meta_vars : ?init:t_ MetaVar.t ID.Map.t -> t_ -> t_ MetaVar.t ID.Map.t
  (** The free type meta-variables in [t] *)

  val fun_unfold : t_ -> t_ Var.t list * t_
  (** [fun_unfold (fun x y z. t) = [x;y;z], t] *)

  val get_ty_arg : t_ -> int -> t_ option
  (** [get_ty_arg ty n] gets the [n]-th argument of [ty], if [ty] is a
      function type with at least [n] arguments. *)

  val ty_unfold : t_ -> t_ Var.t list * t_ list * t_
  (** [ty_unfold ty] decomposes [ty] into a list of quantified type variables,
      a list of parameters, and a return type (which is not an arrow).

      [ty_unfold (forall a b, a -> b -> c -> d)] will return
      [([a;b], [a;b;c], d)]
  *)

  val ty_is_Type : t_ -> bool
  (** t == Type? *)

  val ty_returns_Type : t_ -> bool
  (** t == forall ... -> ... -> ... -> Type? *)

  val ty_returns_Prop : t_ -> bool

  val ty_returns : t_ -> t_
  (** follow forall/arrows to get return type.  *)

  val ty_is_Kind : t_ -> bool
  (** type == Kind? *)

  val ty_is_Prop : t_ -> bool
  (** t == Prop? *)

  val ty_is_unitype : t_ -> bool

  val ty_num_param : t_ -> int
  (** Number of type variables that must be bound in the type. *)
end

(** Utils that only require a {!REPR} *)
module UtilRepr(T : REPR)
: UTIL_REPR with type t_ = T.t
= struct
  type t_ = T.t

  let rec head_sym t = match T.repr t with
    | App (f, _) -> head_sym f
    | Const id -> id
    | _ -> raise Not_found

  let to_seq t yield =
    let rec aux t =
      yield t;
      match T.repr t with
      | TyMeta _ -> ()
      | TyBuiltin _
      | Const _ -> ()
      | Var v -> aux_var v
      | Match (t,l) ->
          aux t;
          ID.Map.iter (fun _ (vars,rhs) -> List.iter aux_var vars; aux rhs) l
      | Builtin b -> Builtin.iter aux b
      | App (f,l) -> aux f; List.iter aux l
      | Bind (_,v,t) -> aux_var v; aux t
      | Let (v,t,u) -> aux_var v; aux t; aux u
      | TyArrow (a,b) -> aux a; aux b
    and aux_var v = aux (Var.ty v)
    in
    aux t

  module VarSet = Var.Set(T)

  let to_seq_free_vars ?(bound=VarSet.empty) t yield =
    let rec aux ~bound t = match T.repr t with
      | Const _ -> ()
      | Var v ->
          if VarSet.mem v bound then () else yield v;
          aux ~bound (Var.ty v)
      | App (f,l) ->
          aux ~bound f; List.iter (aux ~bound) l
      | Match (t,l) ->
          aux ~bound t;
          ID.Map.iter
            (fun _ (vars,rhs) ->
              List.iter (fun v -> aux ~bound (Var.ty v)) vars;
              let bound = List.fold_right VarSet.add vars bound in
              aux ~bound rhs
            ) l
      | Builtin b -> Builtin.iter (aux ~bound) b
      | Bind (_,v,t) ->
          aux ~bound (Var.ty v); aux ~bound:(VarSet.add v bound) t
      | Let (v,t,u) ->
          aux ~bound (Var.ty v); aux ~bound t; aux ~bound:(VarSet.add v bound) u
      | TyBuiltin _ -> ()
      | TyArrow (a,b) -> aux ~bound a; aux ~bound b
      | TyMeta _ -> ()
    in
    aux ~bound t

  let to_seq_consts t =
    to_seq t
    |> Sequence.filter_map
      (fun t -> match T.repr t with
         | Const id -> Some id
         | _ -> None)

  let free_vars ?bound t =
    to_seq_free_vars ?bound t |> VarSet.of_seq

  let is_var t = match T.repr t with Var _ -> true | _ -> false
  let is_const t = match T.repr t with Const _ -> true | _ -> false

  let is_closed t = to_seq_free_vars t |> Sequence.is_empty

  let is_undefined t = match T.repr t with Builtin (`Undefined_self _) -> true | _ -> false

  let to_seq_vars t =
    to_seq t
    |> Sequence.flat_map
        (fun t -> match T.repr t with
          | Var v
          | Bind (_,v,_)
          | Let (v,_,_) -> Sequence.return v
          | Match (_,l) ->
              let open Sequence.Infix in
              ID.Map.to_seq l >>= fun (_,(vars,_)) -> Sequence.of_list vars
          | Builtin _
          | Const _
          | App _
          | TyBuiltin _
          | TyArrow (_,_)
          | TyMeta _ -> Sequence.empty
        )

  let to_seq_meta_vars t =
    to_seq t
    |> Sequence.filter_map
        (fun t -> match T.repr t with
          | TyMeta v -> Some v
          | Var _
          | Bind _
          | Builtin _
          | Const _
          | Let _
          | Match _
          | App _
          | TyBuiltin _
          | TyArrow (_,_) -> None
        )

  let free_meta_vars ?(init=ID.Map.empty) t =
    to_seq_meta_vars t
      |> Sequence.fold
          (fun acc v -> ID.Map.add (MetaVar.id v) v acc)
          init

  let fun_unfold t =
    let rec aux vars t = match T.repr t with
      | Bind (`Fun, v, t') -> aux (v::vars) t'
      | _ -> List.rev vars, t
    in
    aux [] t

  let ty_unfold t =
    let rec aux1 t = match T.repr t with
      | TyArrow (l, r) ->
          let args, ret = aux2 r in
          [], l :: args, ret
      | Bind (`TyForall, v, t') ->
          let vs, args, ret = aux1 t' in
          v :: vs, args, ret
      | _ -> [], [], t
    and aux2 t = match T.repr t with
      | TyArrow (l, r) ->
          let args, ret = aux2 r in
          l :: args, ret
      | _ -> [], t
    in
    aux1 t

  let ty_is_Type t = match T.repr t with
    | TyBuiltin `Type -> true
    | _ -> false

  let ty_is_Kind t = match T.repr t with
    | TyBuiltin `Kind -> true
    | _ -> false

  let ty_is_Prop t = match T.repr t with
    | TyBuiltin `Prop -> true
    | _ -> false

  let ty_is_unitype t = match T.repr t with
    | TyBuiltin `Unitype -> true
    | _ -> false

  let rec ty_returns t = match T.repr t with
    | TyArrow (_, t') -> ty_returns t'
    | Bind (`TyForall, _, t') -> ty_returns t'
    | _ -> t

  let ty_returns_Type t = match T.repr (ty_returns t) with
    | TyBuiltin `Type -> true
    | _ -> false

  let ty_returns_Prop t = match T.repr (ty_returns t) with
    | TyBuiltin `Prop -> true
    | _ -> false

  let rec get_ty_arg ty i = match T.repr ty with
    | App (_,_)
    | TyBuiltin _
    | Const _
    | Var _
    | TyMeta _ -> None
    | TyArrow (a,b) ->
        if i=0 then Some a else get_ty_arg b (i-1)
    | Bind (`TyForall, _,_) -> None
    | _ -> assert false

  (* number of parameters of this (polymorphic?) T.t type *)
  let rec ty_num_param ty = match T.repr ty with
    | TyMeta _ -> 0
    | Var _ -> 0
    | Const _
    | App _
    | TyBuiltin _ -> 0
    | TyArrow (a,t') ->
        if ty_is_Type a
        then 1 + ty_num_param t' (* [a] is a type parameter *)
        else 0 (* asks for term parameters *)
    | Bind (`TyForall, _,t) -> 1 + ty_num_param t
    | _ -> assert false
end

exception Undefined of id
(** When a symbol is not defined *)

let () = Printexc.register_printer
  (function
    | Undefined id -> Some ("undefined ID: " ^ ID.to_string id)
    | _ -> None
  )

module type UTIL = sig
  include UTIL_REPR

  val build : t_ view -> t_
  val const : id -> t_
  val builtin : t_ Builtin.t -> t_
  val app_builtin : t_ Builtin.t -> t_ list -> t_
  val var : t_ var -> t_
  val app : t_ -> t_ list -> t_
  val app_const : ID.t -> t_ list -> t_
  val fun_ : t_ var -> t_ -> t_
  val mu : t_ var -> t_ -> t_
  val let_ : t_ var -> t_ -> t_ -> t_
  val match_with : t_ -> t_ cases -> t_
  val ite : t_ -> t_ -> t_ -> t_
  val forall : t_ var -> t_ -> t_
  val exists : t_ var -> t_ -> t_

  val eq : t_ -> t_ -> t_
  val neq : t_ -> t_ -> t_
  val imply : t_ -> t_ -> t_
  val imply_l : t_ list -> t_ -> t_
  val true_ : t_
  val false_ : t_
  val and_ : t_ list -> t_
  val or_ : t_ list -> t_
  val not_ : t_ -> t_
  val undefined_self : t_ -> t_ (** fresh undefined term *)
  val undefined_atom : ty:t_ -> t_ (** fresh undefined constant *)
  val data_test : ID.t -> t_ -> t_
  val data_select : ID.t -> int -> t_ -> t_
  val unparsable : ty:t_ -> t_

  val and_nodup : t_ list -> t_

  val asserting : t_ -> t_ list -> t_
  val assuming : t_ -> t_ list -> t_
  val guard : t_ -> t_ Builtin.guard -> t_

  val mk_bind : Binder.t -> t_ var -> t_ -> t_

  val ty_type : t_ (** Type of types *)
  val ty_kind : t_ (** Type of ty_type *)
  val ty_prop : t_ (** Propositions *)
  val ty_unitype : t_

  val ty_builtin : TyBuiltin.t -> t_
  val ty_const : id -> t_
  val ty_app : t_ -> t_ list -> t_
  val ty_arrow : t_ -> t_ -> t_
  val ty_arrow_l : t_ list -> t_ -> t_
  val ty_var : t_ var -> t_
  val ty_meta : t_ MetaVar.t -> t_
  val ty_forall : t_ var -> t_ -> t_

  val fun_l : t_ var list -> t_ -> t_
  val forall_l : t_ var list -> t_ -> t_
  val exists_l : t_ var list -> t_ -> t_
  val ty_forall_l : t_ var list -> t_ -> t_
  val let_l : (t_ var * t_) list -> t_ -> t_

  val close_forall : t_ -> t_
  (** [close_forall t] universally quantifies over free variables of [t] *)

  val hash_fun : t_ CCHash.hash_fun
  val hash : t_ -> int
  (** Hash into a positive integer *)

  val hash_fun_alpha_eq : t_ CCHash.hash_fun
  val hash_alpha_eq : t_ -> int
  (** Hash function that is not sensitive to alpha-renaming *)

  val equal : t_ -> t_ -> bool
  (** Syntactic equality *)

  (** {2 Misc} *)

  module Tbl : CCHashtbl.S with type key = t_
  (** Hashtbl with terms as key. The hash function is modulo α-equiv *)

  val remove_dup : t_ list -> t_ list
  (** Use a hashset to remove duplicates from the list. Order is
      not preserved. *)

  (** {6 Traversal} *)

  val fold :
    f:('acc -> 'b_acc -> t_ -> 'acc) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc) ->
    'acc ->
    'b_acc ->
    t_ ->
    'acc
  (** Non recursive fold.
      @param bind updates the binding accumulator with the bound variable
      @param f used to update the regular accumulator (that is returned) *)

  val iter :
    f:('b_acc -> t_ -> unit) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc) ->
    'b_acc ->
    t_ ->
    unit
  (** Non recursive iter.
      @param bind updates the binding accumulator with the bound variable
      @param f called on immediate subterms and on the regular accumulator *)

  val map' :
    f:('b_acc -> t_ -> 'a) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc * 'a Var.t) ->
    'b_acc ->
    t_ ->
    'a view
  (** Non recursive polymorphic map, returning a new view. Combine with
        {!T.build} in the special case of terms.
      @param f maps a term to a term
      @param bind updates the binding accumulator and returns a new variable *)

  val map :
    f:('b_acc -> t_ -> t_) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc * t_ Var.t) ->
    'b_acc -> t_ -> t_
  (** Special version of {!map'} for terms *)

  val map_pol :
    f:('b_acc -> Polarity.t -> t_ -> t_) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc * t_ Var.t) ->
    'b_acc ->
    Polarity.t ->
    t_ ->
    t_
  (** Similar to {!map} but also keeping the subterm polarity *)

  val approx_infinite_quant_pol :
    [`Forall|`Exists|`Eq] ->
    Polarity.t ->
    [`Unsat_means_unknown of t_ | `Keep]
  (** Approximation of [q] under the polarity [pol]: either

      - [`Unsat_means_unknown replacement] means that we lost completeness,
          and should return [replacement] instead
      - [`Keep] means to keep the quantifier as is *)

  val size : t_ -> int
  (** Number of AST nodes *)

  (** {6 Substitution Utils} *)

  type subst = (t_, t_) Var.Subst.t
  type renaming = (t_, t_ Var.t) Var.Subst.t

  val equal_with : subst:subst -> t_ -> t_ -> bool
  (** Equality modulo substitution *)

  val deref : subst:subst -> t_ -> t_
  (** [deref ~subst t] dereferences [t] as long as it is a variable
      bound in [subst]. *)

  val rename_var : subst -> t_ Var.t -> subst * t_ Var.t
  (** Same as {!Subst.rename_var} but wraps the renamed var in a term *)

  type apply_error = {
    ae_msg: string;
    ae_term: t_ option;
    ae_ty: t_;
    ae_args: t_ list;
    ae_args_ty: t_ list; (* same length as ae_args *)
    ae_subst: subst;
  }

  exception ApplyError of apply_error
  (** Raised when a type application fails *)

  val eval : ?rec_:bool -> subst:subst -> t_ -> t_
  (** Applying a substitution
      @param rec_ if true, when replacing [v] with [t]
        because [(v -> t) in subst], we call [eval subst t] instead of
        assuming [t] is preserved by subst (default false) *)

  val eval_renaming : subst:renaming -> t_ -> t_
  (** Applying a variable renaming *)

  val renaming_to_subst : renaming -> subst

  val ty_apply : t_ -> terms:t_ list -> tys:t_ list -> t_
  (** [apply t ~terms ~tys] computes the type of [f terms] for some
      function [f], where [f : t] and [terms : ty].
      @raise ApplyError if the arguments do not match *)

  val ty_apply_full : t_ -> terms:t_ list -> tys:t_ list -> t_ * subst
  (** [ty_apply_full ty l] is like [apply t l], but it returns a pair
      [ty' , subst] such that [subst ty' = apply t l].
      @raise ApplyError if the arguments do not match *)

  val ty_apply_mono : t_ -> tys:t_ list -> t_
  (** [apply t ~tys] computes the type of [f terms] for some
      function [f], where [f : t] and [terms : ty].
      @raise Invalid_argument if [t] is not monomorphic (i.e. not TyForall)
      @raise ApplyError if the arguments do not match *)

  type signature = id -> t_ option
  (** A signature is a way to obtain the type of a variable *)

  val ty : sigma:signature -> t_ -> t_ or_error
  (** Compute the type of the given term in the given signature. *)

  val ty_exn : sigma:signature -> t_ -> t_
  (** Same as {!ty} but unsafe.
      @raise Failure in case of error at an application
      @raise Undefined in case some symbol is not defined *)

  exception UnifError of string * t_ * t_
  (** Raised for unification or matching errors *)

  val match_exn : ?subst2:subst -> t_ -> t_ -> subst
  (** [match_exn ~subst2 t1 t2] matches the pattern [t1] against [subst2 t2].
      Variables in [subst2 t2] are not bound.
      We assume [t1] and [subst2 t2] do not share variables, and we assume
      that [t1] is a mostly first-order {b pattern} (no binders, but variables
      in head position is accepted and will only match an application).
      @raise UnifError if they dont_ match
      @raise Invalid_argument if [t1] is not a valid pattern *)

  val match_ : ?subst2:subst -> t_ -> t_ -> subst option
  (** Safe version of {!match_exn}
      @raise Invalid_argument if [t1] is not a valid pattern *)

  (* TODO: unification *)
end

module Util(T : S)
: UTIL with type t_ = T.t
= struct
  include UtilRepr(T)

  let ty_type = T.build (TyBuiltin `Type)
  let ty_kind = T.build (TyBuiltin `Kind)
  let ty_prop = T.build (TyBuiltin `Prop)
  let ty_unitype = T.build (TyBuiltin `Unitype)

  let build = T.build
  let const id = T.build (Const id)
  let var v = T.build (Var v)
  let app t l = match l with
    | [] -> t
    | _::_ -> T.build (App(t,l))
  let app_const id l = app (const id) l
  let mk_bind b v t = T.build (Bind (b, v, t))
  let fun_ v t = T.build (Bind (`Fun, v, t))
  let mu v t = T.build (Bind (`Mu, v, t))

  let let_ v t u = match T.repr u with
    | Builtin `True
    | Builtin `False -> u
    | _ -> T.build (Let (v, t, u))

  let match_with t l =
    if ID.Map.is_empty l then invalid_arg "Term.case: empty list of cases";
    T.build (Match (t,l))

  let forall v t = match T.repr t with
    | Builtin `True
    | Builtin `False -> t
    | _ -> T.build (Bind(`Forall,v, t))

  let exists v t = match T.repr t with
    | Builtin `True
    | Builtin `False -> t
    | _ -> T.build (Bind(`Exists,v, t))

  exception FlattenExit of T.t

  let flatten (b:[<`And | `Or]) l =
    try
      CCList.flat_map
        (fun t -> match T.repr t with
          | Builtin `True when b=`And -> []
          | Builtin `True when b=`Or -> raise (FlattenExit t) (* shortcut *)
          | Builtin `False when b=`Or -> []
          | Builtin `False when b=`And -> raise (FlattenExit t)
          | Builtin (`And l') when b=`And -> l'
          | Builtin (`Or l') when b=`Or -> l'
          | _ -> [t])
        l
    with FlattenExit t ->
      [t]

  let builtin_ b = T.build (Builtin b)
  let app_builtin_ b l = app (builtin_ b) l

  let true_ = builtin_ `True
  let false_ = builtin_ `False

  let rec builtin arg = match arg with
    | `Ite (a,b,c) ->
        begin match T.repr a, T.repr b, T.repr c with
        | Builtin `True, _, _ -> b
        | Builtin `False, _, _ -> c
        | _, Builtin `True, Builtin `False -> a
        | _, Builtin `False, Builtin `True -> not_ a
        | _, Builtin `True, Builtin `True -> true_
        | _, Builtin `False, Builtin `False -> false_
        | _, Builtin `True, _ -> or_ [a; c] (* then branch: true *)
        | _, Builtin `False, _ -> and_ [not_ a; c] (* then branch: false *)
        | _, _, Builtin `True -> imply a b (* else branch: true *)
        | _, _, Builtin `False -> and_ [a; b] (* else branch: false *)
        | _ -> builtin_ arg
        end
    | `Eq (a,b) ->
        begin match T.repr a, T.repr b with
        | Builtin `True, _ -> b
        | _, Builtin `True -> a
        | Builtin `False, _ -> not_ b
        | _, Builtin `False -> not_ a
        | _ -> builtin_ arg
        end
    | `And l ->
        begin match flatten `And l with
        | [] -> true_
        | [x] -> x
        | l -> builtin_ (`And l)
        end
    | `Or l ->
        begin match flatten `Or l with
        | [] -> false_
        | [x] -> x
        | l -> builtin_ (`Or l)
        end
    | `Not t ->
        begin match T.repr t with
        | Builtin `True -> false_
        | Builtin `False -> true_
        | Builtin (`And l) -> or_ (List.map not_ l)
        | Builtin (`Or l) -> and_ (List.map not_ l)
        | Builtin (`Not t) -> t
        | _ -> builtin_ (`Not t)
        end
    | `Imply (a,b) ->
        begin match T.repr a, T.repr b with
        | Builtin `True, _ -> b
        | Builtin `False, _ -> true_
        | _, Builtin `True -> true_
        | _, Builtin `False -> not_ a
        | _ -> builtin_ (`Imply (a,b))
        end
    | _ -> builtin_ arg

  and app_builtin arg l = match arg, l with
    | (`Ite _ | `Eq _), [] -> builtin arg
    | _ -> app_builtin_ arg l

  and not_ t = builtin (`Not t)
  and and_ l = builtin (`And l)
  and or_ l = builtin (`Or l)
  and imply a b = builtin (`Imply (a,b))

  let imply_l l ret = match l with
    | [] -> ret
    | [a] -> imply a ret
    | _ -> imply (and_ l) ret

  let eq a b = builtin (`Eq (a,b))
  let neq a b = not_ (eq a b)
  let ite a b c = app_builtin (`Ite (a,b,c)) []

  let undefined_self t =
    let id = ID.make "_" in
    builtin (`Undefined_self (id,t))

  let undefined_atom ~ty =
    let id = ID.make "_" in
    builtin (`Undefined_atom (id,ty))

  let data_test c t = app_builtin (`DataTest c) [t]
  let data_select c i t = app_builtin (`DataSelect (c,i)) [t]
  let unparsable ~ty = builtin (`Unparsable ty)

  let guard t g =
    let open Builtin in
    match T.repr t, g.asserting, g.assuming with
    | _, [], [] -> t
    | Builtin (`Guard (t', g')), _, _ ->
        let g'' = Builtin.merge_guard g g' in
        builtin (`Guard (t', g''))
    | _ ->
        builtin (`Guard (t, g))

  let asserting t p = guard t {Builtin. asserting=p; assuming=[]}
  let assuming t p = guard t {Builtin. assuming=p; asserting=[]}

  let ty_builtin b = T.build (TyBuiltin b)
  let ty_const id = const id
  let ty_app f l = if l=[] then f else app f l
  let ty_arrow a b = T.build (TyArrow (a,b))
  let ty_arrow_l args ret = List.fold_right ty_arrow args ret
  let ty_forall v t = T.build (Bind (`TyForall,v,t))
  let ty_var v = T.build (Var v)
  let ty_meta v = T.build (TyMeta v)

  let fun_l = List.fold_right fun_
  let forall_l = List.fold_right forall
  let exists_l = List.fold_right exists
  let ty_forall_l = List.fold_right ty_forall
  let let_l l = List.fold_right (fun (v,t) u -> let_ v t u) l

  let close_forall t =
    let fvars = free_vars t |> VarSet.to_list in
    forall_l fvars t

  let hash_fun_ hash_var t h =
    let d = ref 30 in (* number of nodes to explore *)
    let rec hash_ t h =
      if !d = 0 then h
      else match T.repr t with
        | Const id -> decr d; ID.hash_fun id h
        | Var v -> decr d; hash_var v h
        | App (f,l) -> hash_ f h |> CCHash.list hash_ l
        | Builtin b -> CCHash.seq hash_ (Builtin.to_seq b) h
        | Let (v,t,u) -> decr d; hash_var v h |> hash_ t |> hash_ u
        | Bind (_,v,t) -> decr d; hash_var v h |> hash_ t
        | Match (t,l) ->
            decr d;
            hash_ t h
              |> CCHash.seq
                (fun (vars,rhs) h -> CCHash.list hash_var vars h |> hash_ rhs)
                (ID.Map.to_seq l |> Sequence.map snd)
        | TyArrow (a,b) -> decr d; hash_ a h |> hash_ b
        | TyBuiltin _
        | TyMeta _ -> h
    in
    hash_ t h

  let hash_fun =
    let hash_var_ v h = ID.hash_fun (Var.id v) h in
    hash_fun_ hash_var_

  let hash_fun_alpha_eq =
    let hash_var_ _ h = CCHash.string "var" h in
    hash_fun_ hash_var_

  let hash t = CCHash.apply hash_fun t
  let hash_alpha_eq t = CCHash.apply hash_fun_alpha_eq t

  module Subst = Var.Subst

  type subst = (T.t, T.t) Subst.t
  type renaming = (t_, t_ Var.t) Var.Subst.t

  let rename_var subst v =
    let v' = Var.fresh_copy v in
    Subst.add ~subst v (var v'), v'

  let rec equal_with ~subst ty1 ty2 =
    match T.repr ty1, T.repr ty2 with
    | Const id1, Const id2 -> ID.equal id1 id2
    | Var v1, _ when Subst.mem ~subst v1 ->
        equal_with ~subst (Subst.find_exn ~subst v1) ty2
    | _, Var v2 when Subst.mem ~subst v2 ->
        equal_with ~subst ty1 (Subst.find_exn ~subst v2)
    | Var v1, Var v2 -> Var.equal v1 v2
    | Builtin b1, Builtin b2 -> Builtin.equal (equal_with ~subst) b1 b2
    | TyBuiltin b1, TyBuiltin b2 -> TyBuiltin.equal b1 b2
    | TyMeta v1, TyMeta v2 -> MetaVar.equal v1 v2
    | App (f1,l1), App (f2, l2) ->
        equal_with ~subst f1 f2
          && List.length l1 = List.length l2
          && List.for_all2 (equal_with ~subst) l1 l2
    | TyArrow (a1,b1), TyArrow (a2,b2) ->
        equal_with ~subst a1 a2 && equal_with ~subst b1 b2
    | Bind (b1, v1, t1), Bind (b2, v2, t2) ->
        b1 = b2 &&
        ( let v = Var.fresh_copy v1 in
          let subst = Subst.add ~subst v1 (var v) in
          let subst = Subst.add ~subst v2 (var v) in
          equal_with ~subst t1 t2)
    | Let (v1,t1,u1), Let (v2,t2,u2) ->
        let subst = Subst.add ~subst v1 t1 in
        let subst = Subst.add ~subst v2 t2 in
        equal_with ~subst u1 u2
    | Match (t1,l1), Match (t2,l2) ->
        ID.Map.cardinal l1 = ID.Map.cardinal l2 &&
        equal_with ~subst t1 t2 &&
        List.for_all2
          (fun (id1,(vars1,rhs1)) (id2,(vars2,rhs2)) ->
            assert (List.length vars1=List.length vars2);
            ID.equal id1 id2
            &&
            let subst = List.fold_right2
              (fun v1 v2 subst ->
                let v = Var.fresh_copy v1 in
                let subst = Subst.add ~subst v1 (var v) in
                let subst = Subst.add ~subst v2 (var v) in
                subst
              ) vars1 vars2 subst
            in
            equal_with ~subst rhs1 rhs2
          )
          (cases_to_list l1) (* list, sorted by ID *)
          (cases_to_list l2)
    | Var _, _
    | Match _, _
    | TyBuiltin _,_
    | Builtin _,_
    | Const _,_
    | App (_,_),_
    | Let (_,_,_),_
    | TyArrow (_,_),_
    | Bind _, _
    | TyMeta _,_ -> false

  let equal a b = equal_with ~subst:Subst.empty a b

  module Tbl = CCHashtbl.Make(struct
      type t = t_
      let equal = equal
      let hash = hash_alpha_eq
    end)

  (* remove duplicates in [l] *)
  let remove_dup l : t_ list =
    match l with
      | []
      | [_] -> l
      | [t1;t2] -> if equal t1 t2 then [t1] else l
      | _ ->
        let h = Tbl.create 16 in
        List.iter (fun t -> Tbl.replace h t ()) l;
        Tbl.keys_list h

  let and_nodup l =
    flatten `And l
    |> remove_dup
    |> and_

  let fold ~f ~bind acc b_acc t =
    let rec fold_l ~f ~bind acc b_acc = function
      | [] -> acc
      | t :: l' ->
          let acc = f acc b_acc t in
          fold_l ~f ~bind acc b_acc l'
    in
    match T.repr t with
    | TyMeta _
    | Const _
    | TyBuiltin _
    | Var _ -> acc
    | App (hd,l) ->
        let acc = f acc b_acc hd in
        fold_l ~f ~bind acc b_acc l
    | Builtin b -> Builtin.fold ~f:(fun acc t -> f acc b_acc t) ~x:acc b
    | Bind (_,v,t) ->
        let b_acc = bind b_acc v in
        f acc b_acc t
    | Let (v,t,u) ->
        let acc = f acc b_acc t in
        let b_acc = bind b_acc v in
        f acc b_acc u
    | Match (t,cases) ->
        let acc = f acc b_acc t in
        ID.Map.fold
          (fun _ (vars,rhs) acc ->
            let b_acc = List.fold_left bind b_acc vars in
            f acc b_acc rhs)
          cases acc
    | TyArrow (a,b) ->
        let acc = f acc b_acc a in
        f acc b_acc b

  let iter ~f ~bind b_acc t =
    fold () b_acc t ~bind ~f:(fun () b_acc t -> f b_acc t)

  let map' ~f ~bind b_acc t = match T.repr t with
    | TyBuiltin b -> TyBuiltin b
    | Const id -> Const id
    | TyMeta v -> TyMeta (MetaVar.update ~f:(f b_acc) v)
    | Var v -> Var (Var.update_ty ~f:(f b_acc) v)
    | App (hd,l) ->
        let hd = f b_acc hd in
        let l = List.map (f b_acc) l in
        App (hd, l)
    | Builtin b ->
        let b = Builtin.map ~f:(f b_acc) b in
        Builtin b
    | Let (v,t,u) ->
        let t = f b_acc t in
        let b_acc, v' = bind b_acc v in
        let u = f b_acc u in
        Let (v', t, u)
    | Bind (b,v,t) ->
        let b_acc, v' = bind b_acc v in
        let t = f b_acc t in
        Bind (b, v', t)
    | Match (lhs,cases) ->
        let lhs = f b_acc lhs in
        let cases = ID.Map.map
          (fun (vars,rhs) ->
            let b_acc, vars' = Utils.fold_map bind b_acc vars in
            vars', f b_acc rhs)
          cases
        in
        Match (lhs, cases)
    | TyArrow (a,b) ->
        let a = f b_acc a in
        let b = f b_acc b in
        TyArrow (a,b)

  let map ~f ~bind b_acc t = T.build (map' ~f ~bind b_acc t)

  module P = Polarity

  let map_pol ~f ~bind b_acc pol t = match T.repr t with
    | TyBuiltin _
    | Const _
    | TyMeta _ -> t
    | Var v -> var (Var.update_ty ~f:(f b_acc P.NoPol) v)
    | App (hd,l) ->
        begin match T.repr hd, l with
        | Builtin (`DataTest _ | `DataSelect _), [t] ->
            let hd = f b_acc pol hd in
            let t = f b_acc pol t in
            app hd [t]
        | _ ->
            let hd = f b_acc pol hd in
            let l = List.map (f b_acc P.NoPol) l in
            app hd l
        end
    | Builtin (`Unparsable t) -> unparsable ~ty:(f b_acc (P.NoPol) t)
    | Builtin (`Not t) ->
        let t = f b_acc (P.inv pol) t in
        not_ t
    | Builtin (`Or l) ->
        let l = List.map (f b_acc pol) l in
        or_ l
    | Builtin (`And l) ->
        let l = List.map (f b_acc pol) l in
        and_ l
    | Builtin (`Imply (a,b)) ->
        let a = f b_acc (P.inv pol) a in
        let b = f b_acc pol b in
        imply a b
    | Builtin (`True | `False | `DataSelect _ | `DataTest _) ->
       (* partially applied, or constant *)
          t
    | Builtin (`Undefined_self (id,t)) ->
        builtin (`Undefined_self (id, f b_acc P.NoPol t))
    | Builtin (`Undefined_atom (id,t)) ->
        builtin (`Undefined_atom (id, f b_acc P.NoPol t))
    | Builtin (`Guard (t, g)) ->
        let open Builtin in
        let t = f b_acc pol t in
        let g = {
          asserting = List.map (f b_acc P.Pos) g.asserting;
          assuming = List.map (f b_acc P.Neg) g.assuming;
        } in
        guard t g
    | Builtin (`Eq (a,b)) ->
        let a = f b_acc P.NoPol a in
        let b = f b_acc P.NoPol b in
        eq a b
    | Builtin (`Ite (a,b,c)) ->
        let a = f b_acc P.NoPol a in
        let b = f b_acc pol b in
        let c = f b_acc pol c in
        ite a b c
    | Let (v,t,u) ->
        let t = f b_acc P.NoPol t in
        let b_acc, v' = bind b_acc v in
        let u = f b_acc pol u in
        let_ v' t u
    | Bind ((`Forall | `Exists as b), v, t) ->
        let b_acc, v' = bind b_acc v in
        let t = f b_acc pol t in
        mk_bind b v' t
    | Bind ((`TyForall | `Fun | `Mu) as b, v, t) ->
        (* no polarity in those binders *)
        let b_acc, v' = bind b_acc v in
        let t = f b_acc P.NoPol t in
        mk_bind b v' t
    | Match (lhs,cases) ->
        let lhs = f b_acc P.NoPol lhs in
        let cases = ID.Map.map
          (fun (vars,rhs) ->
            let b_acc, vars' = Utils.fold_map bind b_acc vars in
            vars', f b_acc pol rhs)
          cases
        in
        match_with lhs cases
    | TyArrow (a,b) ->
        let a = f b_acc pol a in
        let b = f b_acc pol b in
        ty_arrow a b

  let approx_infinite_quant_pol
      (q:[`Forall|`Exists|`Eq])
      (pol:Polarity.t)
    : [`Unsat_means_unknown of t_ | `Keep] =
    match q, pol with
      | `Forall, P.Neg
      | `Eq, P.Neg
      | `Exists, P.Pos -> `Keep
      | `Forall, P.Pos
      | `Eq, P.Pos
      | `Exists, P.Neg ->
        let res = if pol=P.Pos then false_ else true_ in
        `Unsat_means_unknown res
      | _, P.NoPol ->
        (* aww. no idea, just avoid this branch if possible *)
        let res = asserting false_ [false_] in
        `Unsat_means_unknown res

  let size t =
    let n = ref 0 in
    let rec aux t =
      incr n;
      iter () t ~bind:(fun () _ -> ()) ~f:(fun () t' -> aux t')
    in
    aux t;
    !n

  let rec deref ~subst t = match T.repr t with
    | Var v ->
        begin match Subst.find ~subst v with
        | None -> t
        | Some t' -> deref ~subst t'
        end
    | _ -> t

  let eval ?(rec_=false) ~subst t =
    let rec aux subst t = match T.repr t with
      | Var v ->
          (* NOTE: when dependent types are added, substitution in types
             will be needed *)
          begin match Subst.find ~subst v with
            | None -> t
            | Some t' when rec_ -> aux subst t'
            | Some t' -> t'
          end
      | _ ->
          map subst t
            ~f:aux
            ~bind:(fun subst v ->
              assert (not (Var.Subst.mem ~subst v));
              let v' = Var.fresh_copy v in
              Var.Subst.add ~subst v (var v'), v')
    in
    if Subst.is_empty subst then t else aux subst t

  let eval_renaming ~subst t =
    let rec aux subst t = match T.repr t with
      | Var v ->
          let v' = Subst.deref_rec ~subst v in
          var v'
      | _ ->
          map subst t
            ~f:aux
            ~bind:(fun subst v ->
              assert (not (Var.Subst.mem ~subst v));
              let v' = Var.fresh_copy v in
              Var.Subst.add ~subst v v', v')
    in
    if Subst.is_empty subst then t else aux subst t

  let renaming_to_subst subst = Var.Subst.map ~f:var subst

  type apply_error = {
    ae_msg: string;
    ae_term: t_ option;
    ae_ty: t_;
    ae_args: t_ list;
    ae_args_ty: t_ list; (* same length as ae_args *)
    ae_subst: subst;
  }

  exception ApplyError of apply_error
  (** Raised when a type application fails *)

  exception UnifError of string * T.t * T.t
  (** Raised for unification or matching errors *)

  let () =
    Printexc.register_printer
    (function
      | ApplyError ae ->
          let module P = Print(T) in
          let pp_t out = function
            | None -> ()
            | Some t -> fpf out "`@[%a@]`@ : " P.print t
          in
          let msg = Utils.err_sprintf
            "@[<hv2>type error@ when applying @[%a%a@]@ on @[%a : %a@]@ in subst @[%a@]: %s@]"
            pp_t ae.ae_term P.print_in_app ae.ae_ty
            (CCFormat.list P.print_in_app) ae.ae_args
            (CCFormat.list P.print_in_app) ae.ae_args_ty
            (Subst.print P.print) ae.ae_subst ae.ae_msg
          in Some msg
      | UnifError (msg, t1, t2) ->
          let module P = Print(T) in
          let msg = CCFormat.sprintf
            "@[<hv2>unification error@ for %a@ and@ %a: %s@]"
              P.print_in_app t1 P.print_in_app t2 msg
          in Some msg
      | _ -> None
    )

  let error_apply_ ae = raise (ApplyError ae)
  let error_unif_ msg t1 t2 = raise (UnifError (msg, t1, t2))

  let ty_apply_full t ~terms:l_terms ~tys:l_tys =
    let rec app_ ~subst t l_terms l_tys = match T.repr t, l_terms, l_tys with
      | _, [], [] -> t, subst
      | _, [], _ | _, _, [] -> assert false
      | TyBuiltin _, _, _
      | App (_,_),_, _
      | Const _, _, _ ->
          error_apply_
            {ae_msg="cannot apply this type"; ae_term=None;
             ae_ty=t; ae_args=l_terms; ae_args_ty=l_tys; ae_subst=subst}
      | Var v, _, _ ->
          begin try
            let t = Subst.find_exn ~subst v in
            app_ ~subst t l_terms l_tys
          with Not_found ->
            error_apply_
              {ae_msg="cannot apply this type"; ae_term=None;
               ae_ty=t; ae_args=l_terms; ae_args_ty=l_tys; ae_subst=subst; }
          end
      | TyMeta _,_,_ -> assert false
      | TyArrow (a, t'), _ :: l_terms', b :: l_tys' ->
          if equal_with ~subst a b
          then app_ ~subst t' l_terms' l_tys'
          else
            error_apply_
              {ae_msg="type mismatch on first argument"; ae_term=None;
               ae_ty=t; ae_args=l_terms; ae_args_ty=l_tys; ae_subst=subst; }
      | Bind (`TyForall, v, t'), b :: l_terms', _ :: l_tys' ->
          let subst = Subst.add ~subst v b in
          app_ ~subst t' l_terms' l_tys'
      | _ -> assert false
    in
    app_ ~subst:Subst.empty t l_terms l_tys

  let ty_apply t ~terms ~tys =
    let t, subst = ty_apply_full t ~terms ~tys in
    if Subst.is_empty subst then t else eval ~subst t

  let ty_apply_mono t ~tys:l =
    let subst = Subst.empty in
    let rec app_ t l = match T.repr t, l with
      | _, [] -> t
      | TyBuiltin _, _
      | App (_,_),_
      | Const _, _ ->
          error_apply_
            {ae_msg="cannot apply this type"; ae_term=None;
             ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst}
      | Var _, _ ->
          error_apply_
            {ae_msg="cannot apply this type"; ae_term=None;
             ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst}
      | TyMeta _,_ -> assert false
      | TyArrow (a, t'), b :: l' ->
          if equal a b
          then app_ t' l'
          else
            error_apply_
              {ae_msg="type mismatch on first argument"; ae_term=None;
               ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst; }
      | Bind (`TyForall, _, _), _ ->
          error_apply_
            {ae_msg="non monomorphic type"; ae_term=None;
             ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst}
      | _ -> assert false
    in
    app_ t l

  type signature = id -> T.t option

  let find_ty_ ~sigma id = match sigma id with
    | Some ty -> ty
    | None -> raise (Undefined id)

  let prop = ty_prop

  let rec ty_exn ~sigma t =
    match T.repr t with
    | Const id -> find_ty_ ~sigma id
    | Builtin b ->
        begin match b with
          | `Imply (_,_)
          | `Or _
          | `And _
          | `Not _ -> prop
          | `True
          | `False -> prop
          | `Unparsable ty -> ty
          | `Ite (_,b,_) -> ty_exn ~sigma b
          | `Eq (_,_) -> prop
          | `DataTest id ->
              (* id: a->b->tau, where tau inductive; is-id: tau->prop *)
              let ty = find_ty_ ~sigma id in
              ty_arrow (ty_returns ty) prop
          | `DataSelect (id,n) ->
              (* id: a_1->a_2->tau, where tau inductive; select-id-i: tau->a_i*)
              let ty = find_ty_ ~sigma id in
              begin match get_ty_arg ty n with
              | Some ty_arg ->
                  ty_arrow (ty_returns ty) ty_arg
              | _ ->
                  failwith "cannot infer type, wrong argument to DataSelect"
              end
          | `Undefined_self (_,t) -> ty_exn ~sigma t
          | `Undefined_atom (_,ty) -> ty
          | `Guard (t, _) -> ty_exn ~sigma t
        end
    | Var v -> Var.ty v
    | App (_, []) -> assert false
    | App (f,l) ->
        let ty_f = ty_exn ~sigma f in
        let tys = List.map (ty_exn ~sigma) l in
        begin
          try ty_apply ty_f ~terms:l ~tys
          with ApplyError ae ->
            let ae = {ae with ae_term=Some f; ae_args=l; ae_args_ty=tys; ae_ty=ty_f} in
            raise (ApplyError ae)
        end
    | Bind (b,v,t) ->
        begin match b with
        | `Forall
        | `Exists
        | `Mu -> ty_exn ~sigma t
        | `Fun ->
            if ty_returns_Type (Var.ty v)
            then ty_forall v (ty_exn ~sigma t)
            else ty_arrow (Var.ty v) (ty_exn ~sigma t)
        | `TyForall -> ty_type
        end
    | Let (_,_,u) -> ty_exn ~sigma u
    | Match (_,m) ->
        let _, (_, rhs) = ID.Map.choose m in
        ty_exn ~sigma rhs
    | TyMeta _ -> assert false
    | TyBuiltin b ->
        begin match b with
        | `Kind -> failwith "Term_ho.ty: kind has no type"
        | `Type -> ty_kind
        | `Prop
        | `Unitype -> ty_type
        end
    | TyArrow (_,_) -> ty_type

  let ty ~sigma t =
    try CCResult.return (ty_exn ~sigma t)
    with e -> Utils.err_of_exn e

  (* return lists of same length, for
    unification or matching in the case of application *)
  let unif_l_ f1 l1 f2 l2 =
    let n1 = List.length l1 in
    let n2 = List.length l2 in
    if n1=n2 then f1::l1, f2::l2
    else if n1<n2 then
      let l2_1, l2_2 = CCList.take_drop (n2-n1) l2 in
      f1::l1, (app f2 l2_1) :: l2_2
    else
      let l1_1, l1_2 = CCList.take_drop (n1-n2) l1 in
      (app f1 l1_1) :: l1_2, f2 :: l2

  let match_exn ?(subst2=Subst.empty) t1 t2 =
    (* bound: bound variables in t1 and t2 *)
    let rec match_ subst t1 t2 =
      let t2 = deref ~subst:subst2 t2 in
      match T.repr t1, T.repr t2 with
      | Builtin b1, Builtin b2 ->
          Builtin.fold2 b1 b2 ~x:subst
            ~fail:(fun () -> error_unif_ "do not match" t1 t2)
            ~f:match_
      | Const id1, Const id2 when ID.equal id1 id2 -> subst
      | Var v1, _ -> match_var subst v1 t1 t2
      | App (f1, l1), App (f2, l2) ->
          (* right-parenthesed application *)
          let l1, l2 = unif_l_ f1 l1 f2 l2 in
          List.fold_left2 match_ subst l1 l2
      | TyArrow (a1, b1), TyArrow (a2,b2) ->
          let subst = match_ subst a1 a2 in
          match_ subst b1 b2
      | Bind _, _ -> invalid_arg "pattern is not first-order"
      | Let (_, _, _), _
      | Match _, _ -> invalid_arg "pattern is not first-order"
      | TyBuiltin b1, TyBuiltin b2 when TyBuiltin.equal b1 b2 -> subst
      | TyMeta _, _ -> assert false
      | Builtin _, _
      | Const _, _
      | App (_, _), _
      | TyArrow _, _
      | TyBuiltin _, _ -> error_unif_ "do not match" t1 t2
    and match_var subst v t1 t2 =
      match Subst.find ~subst v with
      | None ->
          (* NOTE: no occur check, we assume t1 and t2 share no variables *)
          Subst.add ~subst v t2
      | Some t1' ->
          if equal_with ~subst t1' t2
            then subst
            else error_unif_ "incompatible variable binding" t1 t2
    in
    match_ Subst.empty t1 t2

  let match_ ?subst2 t1 t2 =
    try Some (match_exn ?subst2 t1 t2)
    with UnifError _ -> None

  (* TODO write test *)
end

(** {2 Default Implementation} *)

module Default : sig
  include S

  module U : UTIL with type t_ = t
  module P : PRINT with type t = t
end = struct
  type t = {
    view: t view;
  }
  type t_ = t

  let rec repr t = match t.view with
    | TyMeta {MetaVar.deref=Some t'; _} -> repr t'
    | v -> v

  let make_raw_ view = {view}

  let build view = match view with
    | App (t, []) -> t
    | App ({view=App (f, l1); _}, l2) ->
        make_raw_ (App (f, l1 @ l2))
    | _ -> make_raw_ view

  module U = Util(struct
      type t = t_
      let repr = repr
      let build = build
    end)
  module P = Print(struct type t = t_ let repr = repr end)
end

let default = (module Default : S)

(** {2 Conversion between two representations} *)

module Convert(T1 : REPR)(T2 : BUILD)
: sig
  val convert : T1.t -> T2.t

  val pipe : unit -> (T1.t, T2.t, 'a, 'a) Transform.t
end = struct
  let rec convert t = T2.build
    ( match T1.repr t with
      | TyBuiltin b -> TyBuiltin b
      | Const id -> Const id
      | Builtin b -> Builtin (Builtin.map ~f:convert b)
      | Var v -> Var (aux_var v)
      | App (f,l) -> App (convert f, List.map convert l)
      | Bind (b,v,t) -> Bind (b, aux_var v, convert t)
      | Let (v,t,u) -> Let (aux_var v, convert t, convert u)
      | Match (t,l) ->
          Match (
            convert t,
            ID.Map.map (fun (vars,rhs) -> List.map aux_var vars, convert rhs) l
          )
      | TyArrow (a,b) -> TyArrow (convert a, convert b)
      | TyMeta v -> TyMeta (aux_meta v)
    )
  and aux_var v = Var.update_ty ~f:convert v
  and aux_meta v = MetaVar.update ~f:convert v

  let pipe () =
    Transform.make ~name:"convert"
      ~encode:(fun t -> convert t, ())
      ~decode:(fun () x -> x)
      ()
end
