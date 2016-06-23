
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to Kodkod} *)

open Nunchaku_core
open Nunchaku_parsers

module Res = Problem.Res
module T = FO.T
module Ty = FO.Ty
module S = Scheduling
module E = CCResult

let name = "kodkod"
let section = Utils.Section.make name

type problem = FO_rel.problem
type res = (FO_rel.expr, FO_rel.sub_universe) Problem.Res.t

module SUMap = CCMap.Make(struct
    type t = FO_rel.sub_universe
    let compare = FO_rel.su_compare
  end)

module StrMap = CCMap.Make(String)
module IntMap = CCMap.Make(CCInt)

(* names used by kodkod, based on arity *)
type kodkod_name = string

type offset = int

type state = {
  name_of_id: kodkod_name ID.Map.t;
    (* map names to kodkod names *)
  id_of_name: ID.t StrMap.t;
    (* map kodkod names to IDs *)
  univ_offsets: offset SUMap.t;
    (* sub-universe -> its offset in the global universe *)
  atom_of_offset: FO_rel.atom IntMap.t;
    (* offset -> atom *)
  univ_size: int;
    (* total size of the universe *)
}

let errorf msg = Utils.failwithf msg

(* compute size of universe + offsets *)
let compute_univ_ pb : int * offset SUMap.t * FO_rel.atom IntMap.t =
  let open Sequence.Infix in
  List.fold_left
    (fun (n,map1,map2) su ->
       let map1 = SUMap.add su n map1 in
       (* add n+i-> atom(su,i) to map2 *)
       let map2 =
         0 -- (su.FO_rel.su_card-1)
         |> Sequence.map (fun i -> n+i, FO_rel.atom su i)
         |> IntMap.add_seq map2
       in
       n + su.FO_rel.su_card, map1, map2)
    (0, SUMap.empty, IntMap.empty)
    pb.FO_rel.pb_univ

(* indices for naming constants by arity *)
type name_map = int StrMap.t

(* find a unique name for some ID of arity [n], update the offsets map *)
let name_of_arity (m:name_map) n: name_map * string =
  let prefix = match n with
    | 0 -> assert false
    | 1 -> "s"
    | 2 -> "r"
    | n -> Printf.sprintf "m%d_" n
  in
  let offset = StrMap.get_or ~or_:0 prefix m in
  let m' = StrMap.add prefix (offset+1) m in
  let name = prefix ^ string_of_int offset in
  m', name

(* map atom names to Kodkodi identifiers *)
let translate_names_ pb =
  let _,n2id,id2n =
    CCVector.fold
      (fun (nm,n2id,id2n) decl ->
         let id = decl.FO_rel.decl_id in
         let nm, name = name_of_arity nm decl.FO_rel.decl_arity in
         nm, StrMap.add name id n2id, ID.Map.add id name id2n
      )
      (StrMap.empty,StrMap.empty,ID.Map.empty)
      pb.FO_rel.pb_decls
  in
  n2id, id2n

(* initialize the state for this particular problem *)
let create_state (pb:FO_rel.problem) : state =
  let univ_size, univ_offsets, atom_of_offset = compute_univ_ pb in
  let id_of_name, name_of_id = translate_names_ pb in
  { name_of_id;
    id_of_name;
    atom_of_offset;
    univ_size;
    univ_offsets;
  }

let fpf = Format.fprintf
let pp_list ~sep pp = CCFormat.list ~sep ~start:"" ~stop:"" pp

(* print in kodkodi syntax *)
let print_pb state pb out () : unit =
  (* local substitution for renaming variables *)
  let subst : (FO_rel.var_ty, string) Var.Subst.t ref = ref Var.Subst.empty in
  let id2name id =
    try ID.Map.find id state.name_of_id
    with Not_found -> errorf "kodkod: no name for `%a`" ID.print id
  and su2offset su =
    try SUMap.find su state.univ_offsets
    with Not_found ->
      errorf "kodkod: no offset for `%a`" FO_rel.print_sub_universe su
  in
  (* print a sub-universe *)
  let rec pp_su out (su:FO_rel.sub_universe): unit =
    let offset = su2offset su in
    let card = su.FO_rel.su_card in
    if offset=0
    then fpf out "u%d" card
    else fpf out "u%d@%d" card offset
  and pp_atom out (a:FO_rel.atom): unit =
    let offset = su2offset a.FO_rel.a_sub_universe in
    fpf out "A%d" (offset + a.FO_rel.a_index)
  and pp_tuple out (tuple:FO_rel.tuple) =
    fpf out "[@[%a@]]" (pp_list ~sep:", " pp_atom) tuple
  and pp_ts out (ts:FO_rel.tuple_set): unit = match ts with
    | FO_rel.TS_all su -> pp_su out su
    | FO_rel.TS_list l ->
      fpf out "{@[%a@]}" (pp_list ~sep:", " pp_tuple) l
    | FO_rel.TS_product l ->
      fpf out "%a" (pp_list ~sep:" -> " pp_ts) l
  and pp_form out = function
    | FO_rel.False -> fpf out "false}"
    | FO_rel.True -> fpf out "true"
    | FO_rel.Eq (a,b) ->
      fpf out "(@[<2>%a@ = %a@])" pp_rel a pp_rel b
    | FO_rel.In (a,b) ->
      fpf out "(@[<2>%a@ in %a@])" pp_rel a pp_rel b
    | FO_rel.Mult (m,e) ->
      let s = match m with
        | FO_rel.M_no -> "no"
        | FO_rel.M_one -> "one"
        | FO_rel.M_lone -> "lone"
        | FO_rel.M_some -> "some"
      in
      fpf out "@[<2>%s@ %a@]" s pp_rel e
    | FO_rel.Not f -> fpf out "(! %a)" pp_form f
    | FO_rel.And (a,b) ->
      fpf out "(@[<2>%a@ && %a@])" pp_form a pp_form b
    | FO_rel.Or (a,b) ->
      fpf out "(@[<2>%a@ || %a@])" pp_form a pp_form b
    | FO_rel.Equiv (a,b) ->
      fpf out "(@[<2>%a@ <=> %a@])" pp_form a pp_form b
    | FO_rel.Forall (v,f) -> pp_binder "all" out v f
    | FO_rel.Exists (v,f) -> pp_binder "some" out v f
  and pp_binder b out v f =
    let n = Var.Subst.size !subst in
    let name = Printf.sprintf "S%d'" n in
    subst := Var.Subst.add ~subst:!subst v name;
    CCFun.finally
      ~h:(fun () -> subst := Var.Subst.remove ~subst:!subst v)
      ~f:(fun () ->
        fpf out "(@[<2>%s [%s : one %a]@ | %a@])"
          b name pp_su (Var.ty v) pp_form f)
  and pp_rel out = function
    | FO_rel.Const id -> CCFormat.string out (id2name id )
    | FO_rel.None_  -> CCFormat.string out "none"
    | FO_rel.Tuple_set ts -> pp_ts out ts
    | FO_rel.Var v ->
      begin match Var.Subst.find ~subst:!subst v with
        | None -> errorf "var `%a` not in scope" Var.print_full v
        | Some s -> CCFormat.string out s
      end
    | FO_rel.Unop (FO_rel.Flip, e) -> fpf out "~ %a" pp_rel e
    | FO_rel.Unop (FO_rel.Trans, e) -> fpf out "* %a" pp_rel e
    | FO_rel.Binop (FO_rel.Union, a, b) ->
      fpf out "(@[<2>%a +@ %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Inter, a, b) ->
      fpf out "(@[<2>%a &@ %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Diff, a, b) ->
      fpf out "(@[<2>%a \\@ %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Join, a, b) ->
      fpf out "(@[<2>%a . %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Product, a, b) ->
      fpf out "(@[<2>%a ->@ %a@])" pp_rel a pp_rel b
    | FO_rel.If (a,b,c) ->
      fpf out "(@[<2>if %a@ then %a@ else %a@])"
        pp_form a pp_rel b pp_rel c
    | FO_rel.Comprehension (_,_) -> assert false (* TODO *)
  in
  (* go! prelude first *)
  fpf out "/* emitted from Nunchaku */@.";
  (* settings *)
  fpf out "solver: \"Lingeling\"@.";
  (* universe *)
  fpf out "univ: u%d@." state.univ_size;
  (* decls *)
  CCVector.iter
    (fun d ->
       let id = d.FO_rel.decl_id in
       let name = ID.Map.find id state.name_of_id in
       fpf out "@[<h>bounds %s /* %a */ : [%a, %a] @."
         name ID.print id pp_ts d.FO_rel.decl_low pp_ts d.FO_rel.decl_high)
    pb.FO_rel.pb_decls;
  (* goal *)
  fpf out "@[<v2>solve@ %a;@]@."
    (pp_list ~sep:" &&" pp_form) pb.FO_rel.pb_goal;
  ()

module A = Ast_kodkod

let find_atom_ state (i:int) : FO_rel.atom =
  try IntMap.find i state.atom_of_offset
  with Not_found -> errorf "model parsing: could not find atom for A%d" i

(* convert the raw parse model into something more usable *)
let convert_model state (m:A.model): (FO_rel.expr,FO_rel.sub_universe) Model.t =
  let module M = Model in
  (* first, convert offsets to proper atoms *)
  let m': FO_rel.atom A.relation list =
    List.rev_map
      (fun r ->
         let rel_dom = List.map (List.map (find_atom_ state)) r.A.rel_dom in
         {r with A.rel_dom; })
      m
  in
  (* now build a proper model *)
  List.fold_left
    (fun m {A.rel_name; rel_dom} ->
       let id =
         try StrMap.find rel_name state.id_of_name
         with Not_found -> errorf "could not find ID corresponding to `%s`" rel_name
       in
       let t = FO_rel.const id in
       let u = FO_rel.tuple_set (FO_rel.ts_list rel_dom) in
       M.add_const m (t,u,M.Symbol_prop))
    M.empty
    m'

module Parser = struct
  module L = Lex_kodkod
  module P = Parse_kodkod

  let parse_errorf lexbuf msg =
    let loc = Location.of_lexbuf lexbuf in
    Parsing_utils.parse_error_ ~loc
      ("kodkod: " ^^ msg)

  type 'a t = Lexing.lexbuf -> 'a

  let filter_ ~msg ~f lexbuf =
    let t = L.token lexbuf in
    match f t with
      | Some x -> x
      | None -> parse_errorf lexbuf "expected %s" msg

  (* expect exactly [t] *)
  let exactly ~msg t = filter_ ~msg ~f:(fun t' -> if t=t' then Some () else None)

  let section : A.section t =
    filter_ ~msg:"outcome" ~f:(function P.SECTION s -> Some s | _ -> None)

  let outcome lexbuf : unit = match section lexbuf with
    | A.S_outcome -> ()
    | _ -> parse_errorf lexbuf "wrong section, expected OUTCOME"

  let instance lexbuf : unit = match section lexbuf with
    | A.S_instance -> ()
    | _ -> parse_errorf lexbuf "wrong section, expected INSTANCES"

  let ident : string t =
    filter_ ~msg:"ident" ~f:(function P.IDENT s -> Some s | _ -> None)

  let colon : unit t = exactly ~msg:"`:`" P.COLON

  (* parse the result from the solver's stdout and errcode *)
  let res state (s:string) (errcode:int) : res * S.shortcut =
    if errcode <> 0
    then
      let msg = CCFormat.sprintf "kodkod failed (errcode %d), stdout:@ `%s`@." errcode s in
      Res.Error (Failure msg), S.Shortcut
    else (
      let delim = "---OUTCOME---" in
      let i = CCString.find ~sub:delim s in
      assert (i>=0);
      let s' = String.sub s i (String.length s - i) in
      let lexbuf = Lexing.from_string s' in
      outcome lexbuf;
      match L.result lexbuf with
        | A.Unsat ->
          (* NOTE: we fixed a maximal cardinal, so maybe there's a bigger model *)
          Res.Unknown, S.No_shortcut
        | A.Sat ->
          (* parse model *)
          instance lexbuf;
          let i = ident lexbuf in
          if i <> "relations"
          then parse_errorf lexbuf "expected `relations`, got `%s`" i;
          colon lexbuf;
          let m = Parse_kodkod.parse_model L.token lexbuf in
          let m = convert_model state m in
          Res.Sat m, S.Shortcut
    )
end

let solve ~deadline state pb : res * Scheduling.shortcut =
  Utils.debug ~section 1 "calling kodkod";
  let now = Unix.gettimeofday() in
  if now +. 0.5 > deadline
  then Res.Timeout, S.No_shortcut
  else (
    (* print the problem *)
    let timeout = deadline -. now in
    let kodkod_timeout = int_of_float (ceil ((deadline -. now) *. 1000.)) in
    let hard_timeout = (int_of_float (timeout +. 1.5)) in
    let cmd =
      Printf.sprintf "ulimit -t %d; kodkodi -max-msecs %d 2>&1"
        hard_timeout kodkod_timeout
    in
    (* call solver, get its stdout and errcode *)
    let fut =
      S.popen cmd
        ~f:(fun (stdin,stdout) ->
          (* send problem *)
          let fmt = Format.formatter_of_out_channel stdin in
          Format.fprintf fmt "%a@." (print_pb state pb) ();
          flush stdin;
          close_out stdin;
          CCIO.read_all stdout)
    in
    match S.Fut.get fut with
      | S.Fut.Done (E.Ok (stdout, errcode)) ->
        Utils.debugf ~lock:true ~section 2
          "@[<2>kodkod exited with %d, stdout:@ `%s`@]"
          (fun k->k errcode stdout);
        Parser.res state stdout errcode
      | S.Fut.Done (E.Error e) ->
        Res.Error e, S.Shortcut
      | S.Fut.Stopped ->
        Res.Timeout, S.No_shortcut
      | S.Fut.Fail e ->
        (* return error *)
        Utils.debugf ~lock:true ~section 1 "@[<2>kodkod failed with@ `%s`@]"
          (fun k->k (Printexc.to_string e));
        Res.Error e, S.Shortcut
  )

let call ?(print_model=false) ?(prio=10) ~print pb =
  let state = create_state pb in
  if print
    then Format.printf "@[<v>kodkod problem:@ ```@ %a@,```@]@." (print_pb state pb) ();
  S.Task.make ~prio
    (fun ~deadline () ->
       let res, short = solve ~deadline state pb in
       Utils.debugf ~section 2 "@[<2>kodkod result:@ %a@]"
         (fun k->k Res.print_head res);
       begin match res with
         | Res.Sat m when print_model ->
           let pp_ty oc _ = CCFormat.string oc "$i" in
           Format.printf "@[<2>@{<Yellow>raw kodkod model@}:@ @[%a@]@]@."
             (Model.print (CCFun.const FO_rel.print_expr) pp_ty) m
         | _ -> ()
       end;
       res, short)

let is_available () =
  try Sys.command "which kodkodi > /dev/null" = 0
  with Sys_error _ -> false

let pipe ?(print_model=false) ~print () =
  let encode pb = call ~print_model ~print pb, () in
  Transform.make
    ~name
    ~encode
    ~decode:(fun _ res -> res)
    ()

