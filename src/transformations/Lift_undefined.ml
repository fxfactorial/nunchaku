
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lift Undefined} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module TyMo = TypeMono.Make(T)

let name = "lift_undefined"

let section = Utils.Section.make name
let error_ msg = failwith (Utils.err_sprintf "%s: %s" name msg)
let errorf_ fmt = CCFormat.ksprintf fmt ~f:error_

type term = T.t
type ty = T.t

type decode_state = {
  unknowns: unit ID.Tbl.t;
  (* set of all the unknowns lifted to toplevel *)
}

(** {2 Encoding} *)

type state = {
  new_decls: (ID.t * ty) CCVector.vector;
  (* new declarations *)
  tbl: ID.t ID.Tbl.t;
  (* [unknown_id -> toplevel-id] *)
  env: (term, ty) Env.t;
  (* environment *)
  decode: decode_state;
  (* for decoding *)
}

let create_state ~env () : state = {
  env;
  tbl=ID.Tbl.create 16;
  new_decls=CCVector.create();
  decode={unknowns=ID.Tbl.create 16};
}

let pop_decls state =
  let new_decls =
    CCVector.to_list state.new_decls
    |> List.rev_map
      (fun (id,ty) -> Stmt.decl ~info:Stmt.info_default ~attrs:[] id ty)
  in
  CCVector.clear state.new_decls;
  new_decls

(* make a new "unknown" *)
let decl_new state old_id ty : ID.t =
  let id = ID.make (TyMo.mangle ~sep:"_" ty) in
  Utils.debugf ~section 5 "(@[declare_new %a:@ `@[%a@]`@])"
    (fun k->k ID.print id P.print ty);
  CCVector.push state.new_decls (id, ty);
  assert (not (ID.Tbl.mem state.tbl old_id));
  ID.Tbl.add state.tbl old_id id;
  ID.Tbl.add state.decode.unknowns id ();
  id

(* given [unknown_self t], find the arguments of the lifted version *)
let find_args (t:term): term list = match T.repr t with
  | TI.Const _ -> []
  | TI.App (_, l) -> l
  | _ ->
    errorf_ "cannot find type arguments for `undefined_self @[%a@]`" P.print t

let encode_term state t =
  let rec aux t = match T.repr t with
    | TI.Builtin (`Undefined_self (id, t)) ->
      let args = find_args t in
      (* find or declare toplevel constant for this particular unknown *)
      let new_id = match ID.Tbl.get state.tbl id with
        | Some new_id -> new_id
        | None ->
          (* declare new id *)
          let ty_args = List.map (U.ty_exn ~env:state.env) args in
          let ty = U.ty_arrow_l ty_args (U.ty_exn ~env:state.env t) in
          decl_new state id ty
      in
      U.app_const new_id args
    | _ ->
      U.map () t ~bind:(fun () v->(),v) ~f:(fun () -> aux)
  in
  aux t

let encode_stmt state stmt =
  let stmt' = Stmt.map stmt ~ty:(fun t->t) ~term:(encode_term state) in
  let new_decls = pop_decls state in
  new_decls @ [stmt']

let encode_pb pb =
  let env = Problem.env pb in
  let state = create_state ~env () in
  let pb' =
    Problem.flat_map_statements pb ~f:(encode_stmt state)
  in
  pb', state.decode



(** {2 Decoding} *)

(* remove from model the values of unknowns *)
let decode_model (state:decode_state) m =
  Model.filter m
    ~values:(fun (t,_,_) -> match T.repr t with
      | TI.Const id -> not (ID.Tbl.mem state.unknowns id)
      | _ -> true)

(** {2 Plumbing} *)

let pipe ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after %s@}:@ %a@]@." name Ppb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.empty () |> C.check_problem)
  in
  let decode st = Problem.Res.map_m ~f:(decode_model st) in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list [Ty, Mono])
    ~map_spec:(fun s->s)
    ~on_encoded
    ~encode:encode_pb
    ~decode
    ()


