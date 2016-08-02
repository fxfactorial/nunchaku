
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Subst = Var.Subst
module T = TI.Default
module U = T.U
module P = T.P
module PStmt = Statement.Print(P)(P)
module Pat = Pattern.Make(T)
module Red = Reduce.Make(T)

type term = T.t
type env = (term,term) Env.t

let name = "elim_multi_eqns"

let section = Utils.Section.make name

exception Error of string

let spf = CCFormat.sprintf

let () = Printexc.register_printer
  (function
    | Error msg ->
        Some (spf "@[<2>elimination of multiple equations:@ %s@]" msg)
    | _ -> None)

let error_ msg = raise (Error msg)
let errorf_ msg = Utils.exn_ksprintf msg ~f:error_

type local_state = {
  root: term; (* term being pattern matched on (for undefined) *)
  mutable renaming: (term, term Var.t) Subst.t;
  env: env;
}

type pattern =
  | P_term of term  (* should be a pattern, we will see *)
  | P_any (* no pattern, always succeeds *)

and ('a, 'b) decision_node =
  | DN_match of ('a, 'b) decision_node_match
  | DN_if of 'b list * 'b list  (* true/false *)
  | DN_bind of 'b list (* only accepts variables *)

and ('a, 'b) decision_node_match = {
  dn_tydef: term Stmt.tydef; (* all constructors required *)
  dn_by_cstor: 'a list ID.Map.t;
  dn_wildcard: 'b list; (* matching anything *)
}

let pp_pat out = function
  | P_any -> Format.fprintf out "_"
  | P_term t -> P.print out t

let dnode_add_wildcard d x = match d with
  | DN_if (l,r) -> DN_if (x::l, x::r)
  | DN_match d -> DN_match { d with dn_wildcard=x :: d.dn_wildcard }
  | DN_bind d -> DN_bind (x::d)

let dnode_add_bool d b x = match d, b with
  | DN_if (l,r), `True -> DN_if (x::l,r)
  | DN_if (l,r), `False -> DN_if (l,x::r)
  | DN_bind _, _
  | DN_match _, _ ->
      errorf_ "@[<2>expected boolean decision node@]"

let dnode_add_cstor d c x = match d with
  | DN_match d ->
      let allowed_cstors = d.dn_tydef.Stmt.ty_cstors in
      if not (ID.Map.mem c allowed_cstors)
      then errorf_ "@[<2>%a is not a constructor of %a@ (these are @[%a@])@]"
        ID.print c ID.print d.dn_tydef.Stmt.ty_id
        (CCFormat.seq ID.print) (ID.Map.to_seq allowed_cstors |> Sequence.map fst);
      (* add [x] to the list [l] of subtrees already present for case [c] *)
      let l = try ID.Map.find c d.dn_by_cstor with Not_found -> [] in
      DN_match { d with dn_by_cstor = ID.Map.add c (x::l) d.dn_by_cstor }
  | DN_if _ -> errorf_ "cannot match against %a, boolean case" ID.print c
  | DN_bind _ ->
      errorf_ "cannot match against %a, variable binding only" ID.print c

let add_renaming ~local_state v v' =
  local_state.renaming <- Subst.add ~subst:local_state.renaming v v';
  ()

(* print function for debugging *)
let pp_quad out (pats,rhs,side,subst) =
  Format.fprintf out "case @[<hv>@[%a@]@ -> `@[%a@]`@ if @[%a@]@ with @[%a@]@]"
    (CCFormat.list pp_pat) pats
    P.print rhs (CCFormat.list P.print) side
    (Subst.print Var.print_full) subst

(* TODO: carry a "path" argument to know which branch we are in,
   that should be useful for error messages and warnings *)

(* transform flat equations into a match tree. *)
let rec compile_equations ~local_state vars l : term =
  match vars, l with
  | _, [] -> U.undefined_self local_state.root (* undefined case *)
  | [], [([], rhs, [], subst)] ->
      (* simple case: no side conditions, one RHS *)
      U.eval_renaming ~subst rhs
  | [], l ->
      (* reverse list, because the first clauses in pattern-match are the
         ones at the end of the list *)
      let l = List.rev_map
        (fun (args,rhs,side,subst) ->
          assert (args=[]);
          rhs,side,subst)
        l
      in
      yield_list ~local_state l
  | v::vars', _ ->
      (* build one node of the decision tree *)
      let dnode =
        Utils.debugf ~section 5
          "@[<2>build decision node for %a:%a @[%a@]@ with @[<1>%a@]@]"
          (fun k->k Var.print_full v P.print (Var.ty v)
            (CCFormat.list Var.print_full) vars'
            (CCFormat.list pp_quad) l);
        let ty = Var.ty v in
        if U.ty_is_Prop ty
        then DN_if ([], []) (* [v] is a prop, we use a if/then/else *)
        else try
          let ty_id = U.head_sym ty in
          (* what does the type of [v] look like? *)
          match Env.def (Env.find_exn ~env:local_state.env ty_id) with
          | Env.Data (_, _, tydef) ->
              (* [v] is a variable of type (co)data, so we use the list
                 of constructors to build a shallow pattern match *)
              DN_match {
                dn_tydef=tydef;
                dn_by_cstor=ID.Map.empty;
                dn_wildcard=[];
              }
          | Env.Fun_def (_,_,_)
          | Env.Fun_spec _
          | Env.Pred _
          | Env.Copy_abstract _
          | Env.Copy_concrete _
          | Env.Cstor (_,_,_,_) ->
              errorf_ "@[`@[%a@]`@ is not a type.@]" ID.print ty_id
          | Env.Copy_ty _
          | Env.NoDef ->
              (* [v] is of a non-matchable type, but we can still bind
                 it to an (opaque) value *)
              DN_bind []
        with Not_found ->
          DN_bind [] (* not an atomic type *)
      in
      let dnode = List.fold_left
        (fun dnode (pats, rhs, side, subst) ->
          let pat, pats = match pats with [] -> assert false | x::y -> x,y in
          match pat with
          | P_any -> dnode_add_wildcard dnode (pats,rhs,side,subst)
          | P_term t ->
              match Pat.repr t with
              | Pattern.Builtin ((`True | `False) as b) ->
                  (* follow the [true] branch *)
                  dnode_add_bool dnode b (pats,rhs,side,subst)
              | Pattern.App (id,sub_pats) ->
                  (* follow the [id] branch *)
                  let sub_pats = List.map (fun x->P_term x) sub_pats in
                  dnode_add_cstor dnode id (sub_pats,pats,rhs,side,subst)
              | Pattern.Var v' ->
                  (* renaming. We try to use [v'] rather than [v] because
                     the name of [v'] is probably more relevant, except
                     if [v] is already renamed to something else . *)
                  let subst = match Subst.find_deref_rec ~subst:local_state.renaming v with
                    | None when Var.equal v v' -> subst
                    | None ->
                        (* v -> v', use [v'] instead of [v] now, in every branch. *)
                        add_renaming ~local_state v v';
                        subst
                    | Some v'' when Var.equal v' v'' -> subst
                    | Some v'' ->
                        Subst.add ~subst v' v'' (* v -> v'' <- v' *)
                  in
                  dnode_add_wildcard dnode (pats,rhs,side,subst)
        )
        dnode l
      in
      let v = Subst.deref_rec ~subst:local_state.renaming v in
      compile_dnode ~local_state v vars' dnode

(* yield the term composed from the list [l] of cases. The first elements
   of [l] are prioritary w.r.t. the later ones. *)
and yield_list ~local_state l = match l with
  | [] -> assert false
  | [t,[],subst] ->
      (* final case *)
      U.eval_renaming ~subst t
  | [t, ((_::_) as sides), subst] ->
      (* final case, but might fail *)
      let else_ = U.undefined_self local_state.root in
      let sides = List.map (U.eval_renaming ~subst) sides in
      U.ite (U.and_ sides) (U.eval_renaming ~subst t) else_
  | (t,[],subst)::_::_ ->
      Utils.warningf Utils.Warn_overlapping_match
        "@[ignore terms following `@[%a@]`, for it has no side condition@]" P.print t;
      U.eval_renaming ~subst t
  | (t, ((_::_) as sides), subst) :: l' ->
      (* try [sides], yielding [t], otherwise fall back on [l'] *)
      let sides = List.map (U.eval_renaming ~subst) sides in
      U.ite (U.and_ sides)
        (U.eval_renaming ~subst t)
        (yield_list ~local_state l')

(* add missing constructors (not explicitely matched upon) to the set
   of cases, complemented with a list of fresh vars, leading to
   the default cases;
   then compile the subtrees *)
and compile_dnode ~local_state v next_vars dn : term = match dn with
| DN_if (l,r) ->
    let l = compile_equations ~local_state next_vars l in
    let r = compile_equations ~local_state next_vars r in
    let v = Subst.deref_rec ~subst:local_state.renaming v in
    U.ite (U.var v) l r
| DN_bind l -> compile_equations ~local_state next_vars l
| DN_match dn when ID.Map.is_empty dn.dn_by_cstor ->
    (* no need to match, use next variables *)
    compile_equations ~local_state next_vars dn.dn_wildcard
| DN_match dn ->
    (* one level of matching *)
    let l = ID.Map.map
      (fun cstor ->
        let id = cstor.Stmt.cstor_name in
        Utils.debugf ~section 5 "compile_dnode for %a on cstor %a"
          (fun k -> k Var.print v ID.print id);
        (* fresh vars for the constructor's arguments *)
        let vars = List.mapi
          (fun i ty -> Var.make ~ty ~name:(spf "v_%d" i))
          cstor.Stmt.cstor_args
        in
        (* the cases that always match *)
        let wildcard_cases = List.map
          (fun (pats,rhs,side,subst) ->
            List.map (fun _ -> P_any) vars @ pats, rhs, side, subst)
          dn.dn_wildcard
        in
        (* does this constructor also have some explicit branches? *)
        let cases =
          try
            let l = ID.Map.find id dn.dn_by_cstor in
            assert (l <> []);
            List.map
              (fun (new_pats,pats,rhs,side,subst) ->
                assert (List.length new_pats=List.length vars);
                new_pats @ pats, rhs, side, subst)
              l
          with Not_found -> []
        in
        let rhs' =
          compile_equations ~local_state
            (vars @ next_vars) (cases @ wildcard_cases)
        in
        (* see whether the variables were renamed *)
        let vars = List.map (Subst.deref_rec ~subst:local_state.renaming) vars in
        vars, rhs')
      dn.dn_tydef.Stmt.ty_cstors
    in
    let v = Subst.deref_rec ~subst:local_state.renaming v in
    U.match_with (U.var v) l

(* @param env the environment for types and constructors
   @param id the symbol being defined
*)
let uniq_eqns
: env:env ->
  id:ID.t ->
  ty:T.t ->
  (term, term) Statement.equations ->
  (term, term) Statement.equations
  = fun ~env ~id ~ty e -> match e with
  | Stmt.Eqn_single _
  | Stmt.Eqn_app _ -> assert false
  | Stmt.Eqn_nested l ->
    (* create fresh vars *)
    let _, ty_args, _ = U.ty_unfold ty in
    let vars =
      List.mapi
        (fun i ty -> Var.makef ~ty "v_%d" i)
        ty_args
    in
    let cases =
      List.map
        (fun (_,args,rhs,side) ->
          (* might need to add some variables in [args] and [rhs] *)
          let eta_expand_args = CCList.drop (List.length args) vars |> List.map U.var in
          let pats = List.map (fun t -> P_term t) (args @ eta_expand_args) in
          pats, Red.app_whnf rhs eta_expand_args, side, Subst.empty)
        l
    and local_state = {
      root=U.app_const id (List.map U.var vars); (* defined term *)
      renaming=Subst.empty;
      env;
    } in
    (* compile equations into flat pattern matches *)
    let new_rhs = compile_equations ~local_state vars cases in
    (* apply global renaming *)
    let new_rhs = U.eval_renaming ~subst:local_state.renaming new_rhs in
    let vars = List.map (Subst.deref_rec ~subst:local_state.renaming) vars in
    Stmt.Eqn_single (vars,new_rhs)

let uniq_eqn_st env st =
  let loc = Stmt.loc st in
  let info = Stmt.info st in
  match Stmt.view st with
  | Stmt.Axiom (Stmt.Axiom_rec l) ->
      Utils.debugf ~section 5 "@[<2>compile equations@ `@[%a@]`@]"
        (fun k->k PStmt.print_rec_defs l);
      let l' = List.map
        (fun def ->
          let d = Stmt.defined_of_rec def in
          let id = Stmt.id_of_defined d in
          let ty = Stmt.ty_of_defined d in
          let rec_eqns = uniq_eqns ~id ~ty ~env def.Stmt.rec_eqns in
          {def with Stmt.rec_eqns; })
        l
      in
      let env = Env.declare_rec_funs ?loc ~env l' in
      env, Stmt.axiom_rec ~info l'
  | Stmt.Axiom (Stmt.Axiom_spec l) ->
      env, Stmt.axiom_spec ~info l
  | Stmt.Axiom (Stmt.Axiom_std l) ->
      env, Stmt.axiom ~info l
  | Stmt.Decl (id,ty,attrs) ->
      let env = Env.declare ?loc ~attrs ~env id ty in
      env, Stmt.decl ~info ~attrs id ty
  | Stmt.TyDef (k,ty) ->
      (* declare (co)data, so it can be used in encoding *)
      let env = Env.def_data ?loc ~env ~kind:k ty in
      env, Stmt.mk_ty_def ~info k ty
  | Stmt.Pred (wf, k, l) ->
      let env = Env.def_preds ?loc ~env ~wf ~kind:k l in
      env, Stmt.mk_pred ~info ~wf k l
  | Stmt.Copy c ->
      let env = Env.add_copy ?loc ~env c in
      env, Stmt.copy ~info c
  | Stmt.Goal g ->
      env, Stmt.goal ~info g

let uniq_eqns_pb pb =
  let _, pb' =
    Problem.fold_map_statements pb
      ~f:uniq_eqn_st ~x:(Env.create())
  in
  pb'

let pipe ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after uniq equations@}: %a@]@." PPb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.empty () |> C.check_problem)
  and decode _ x = decode x in
  Transform.make
    ~on_encoded
    ~input_spec:Transform.Features.(of_list [Eqn, Eqn_nested])
    ~map_spec:Transform.Features.(update Eqn Eqn_single)
    ~name
    ~encode:(fun p ->
      let p = uniq_eqns_pb p in
      p, ()
    ) ~decode
    ()

