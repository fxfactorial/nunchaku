
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

module ID = NunID
module TI = NunTermInner
module Var = NunVar
module Stmt = NunStatement
module Subst = Var.Subst
module Env = NunEnv

type id = NunID.t

type 'a inv1 = <ty:'a; eqn:[`Nested]>
type 'a inv2 = <ty:'a; eqn:[`Single]>

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module Pat = NunPattern.Make(T)

  type term = T.t
  type 'a env = (term,term,<eqn:[`Whatever];ty:'a>) Env.t

  exception Error of string

  let spf = CCFormat.sprintf

  let () = Printexc.register_printer
    (function
      | Error msg ->
          Some ("elimination of multiple equations: " ^ msg)
      | _ -> None)

  let error_ msg = raise (Error msg)
  let errorf_ msg = NunUtils.exn_ksprintf msg ~f:error_

  (* new [`Undefined] instance of [t] *)
  let mk_undefined t =
    let id = ID.make ~name:"u" in
    U.app_builtin (`Undefined id) [t]

  let mk_ite a b c = U.app_builtin `Ite [a;b;c]
  let mk_and l = U.app_builtin `And l

  type 'a local_state = {
    root: term; (* term being pattern matched on (for undefined) *)
    env: 'a env;
  }

  type pattern =
    | P_term of term  (* should be a pattern, we will see *)
    | P_any (* no pattern, always succeeds *)

  type ('a,'b) decision_node = {
    dn_matched: term; (* term being matched *)
    dn_tydef: term Stmt.tydef; (* all constructors required *)
    dn_by_cstor: 'a list ID.Map.t;
    dn_wildcard: 'b list; (* matching anything *)
  }

  let dnode_add_wildcard d x = { d with dn_wildcard=x :: d.dn_wildcard }

  let dnode_add_cstor d c x =
    if not (ID.Map.mem c d.dn_tydef.Stmt.ty_cstors)
      then errorf_ "%a is not a constructor of %a"
        ID.print_name c ID.print_name d.dn_tydef.Stmt.ty_id;
    let l = try ID.Map.find c d.dn_by_cstor with Not_found -> [] in
    { d with dn_by_cstor = ID.Map.add c (x::l) d.dn_by_cstor }

  (* returns a pair [l1, l2] where [l1] contains RHS terms with no side
     conditions, and [l2] contains RHS terms with their condition *)
  let extract_side_conds l =
    let rec aux noside_acc side_acc l = match l with
      | [] -> noside_acc, side_acc
      | (rhs, [], subst) :: l' -> aux ((rhs,subst) :: noside_acc) side_acc l'
      | (rhs, ((_::_) as sides), subst) :: l' ->
          aux noside_acc ((mk_and sides, rhs, subst) :: side_acc) l'
    in
    aux [] [] l

  (* transform flat equations into a match tree. *)
  let rec compile_equations ~local_state vars l : term =
    match vars, l with
    | _, [] -> mk_undefined local_state.root (* undefined case *)
    | [], [([], rhs, [], subst)] ->
        (* simple case: no side conditions, one RHS *)
        U.eval ~subst rhs
    | [], l ->
        let l = List.map
          (fun (args,rhs,side,subst) ->
            assert (args=[]);
            rhs,side,subst)
          l
        in
        (* add side conditions *)
        let noside, side = extract_side_conds l in
        begin match noside, side with
          | (t1,_)::(t2,_)::_, _ ->
              errorf_ "@[ambiguity: terms `@[%a@]`@ and `@[%a@]`@ have no side conditions@]"
                P.print t1 P.print t2
          | [], l ->
              (* try conditions one by one, fail otherwise *)
              let default = mk_undefined local_state.root in
              List.fold_left
                (fun acc (cond,rhs,subst) ->
                  let rhs = U.eval ~subst rhs in
                  mk_ite cond rhs acc)
                default l
          | [rhs,subst], [] ->
              U.eval ~subst rhs
          | [t,_], _::_ ->
              errorf_
                "@[ambiguity: term `@[%a@]`@ has no side conditions,@ but other terms do@]"
                P.print t
        end
    | v::vars', _ ->
        (* obtain the relevant type definition *)
        let tydef =
          let ty_id = U.head_sym (Var.ty v) in
          match Env.def (Env.find_exn ~env:local_state.env ty_id) with
          | Env.Data (_, _, tydef) -> tydef
          | Env.Fun_def (_,_,_)
          | Env.Fun_spec _
          | Env.Cstor (_,_,_,_)
          | Env.NoDef -> errorf_ "%a is not a datatype" ID.print_name ty_id

        in
        (* build one node of the decision tree *)
        let dnode = {
          dn_matched=U.var v;
          dn_tydef=tydef;
          dn_by_cstor=ID.Map.empty;
          dn_wildcard=[];
        } in
        let dnode = List.fold_left
          (fun dnode (pats, rhs, side, subst) ->
            let pat, pats = match pats with [] -> assert false | x::y -> x,y in
            match pat with
            | P_any -> dnode_add_wildcard dnode (pats,rhs,side,subst)
            | P_term t ->
                match Pat.repr t with
                | NunPattern.App (id,sub_pats) ->
                    (* follow the [id] branch *)
                    let sub_pats = List.map (fun x->P_term x) sub_pats in
                    dnode_add_cstor dnode id (sub_pats,pats,rhs,side,subst)
                | NunPattern.Var v' ->
                    (* renaming *)
                    let subst = Subst.add ~subst v' (U.var v) in
                    dnode_add_wildcard dnode (pats,rhs,side,subst)
          )
          dnode l
        in
        compile_dnode ~local_state vars' dnode

  (* add missing constructors (not explicitely matched upon) to the set
     of cases, complemented with a list of fresh vars, leading to
     the default cases;
     then compile the subtrees *)
  and compile_dnode ~local_state next_vars dn : term =
    let l = ID.Map.map
      (fun cstor ->
        let id = cstor.Stmt.cstor_name in
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
        let rhs' =compile_equations ~local_state
          (vars @ next_vars) (cases @ wildcard_cases)
        in
        vars, rhs'
      )
      dn.dn_tydef.Stmt.ty_cstors
    in
    U.match_with dn.dn_matched l

  (* @param env the environment for types and constructors
     @param id the symbol being defined
  *)
  let uniq_eqns
  : type a.
    env:a env ->
    id:id ->
    (term, term, a inv1) NunStatement.equations ->
    (term, term, a inv2) NunStatement.equations
  = fun ~env ~id (Stmt.Eqn_nested l) ->
      (* create fresh vars *)
      let vars = match l with
        | [] -> assert false
        | (_, args, _, _) :: _ ->
            List.mapi
              (fun i a ->
                let ty = U.ty_exn ~sigma:(Env.find_ty ~env) a in
                Var.make ~ty ~name:(spf "v_%d" i))
              args
      in
      let cases =
        List.map
          (fun (_,args,rhs,side) ->
            let pats = List.map (fun t -> P_term t) args in
            pats, rhs, side, Subst.empty)
          l
      and local_state = {
        root=U.app (U.const id) (List.map U.var vars); (* defined term *)
        env;
      } in
      let new_rhs = compile_equations ~local_state vars cases in
      Stmt.Eqn_single (vars,new_rhs)

  let uniq_eqn_st env st =
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        let l' = List.map
          (fun def ->
            let id = def.Stmt.rec_defined.Stmt.defined_head in
            let rec_eqns = uniq_eqns ~id ~env def.Stmt.rec_eqns in
            {def with Stmt.rec_eqns; }
          )
          l
        in
        let env = Env.declare_rec_funs ~env l' in
        env, Stmt.axiom_rec ~info l'
    | Stmt.Axiom (Stmt.Axiom_spec l) ->
        env, Stmt.axiom_spec ~info l
    | Stmt.Axiom (Stmt.Axiom_std l) ->
        env, Stmt.axiom ~info l
    | Stmt.Decl (id,kind,ty) ->
        let env = Env.declare ~env ~kind id ty in
        env, Stmt.mk_decl ~info id kind ty
    | Stmt.TyDef (k,ty) ->
        (* declare (co)data, so it can be used in encoding *)
        let env = Env.def_data ~env ~kind:k ty in
        env, Stmt.mk_ty_def ~info k ty
    | Stmt.Goal g ->
        env, Stmt.goal ~info g

  let uniq_eqns_pb pb =
    let _, pb' = NunProblem.fold_map_statements pb
      ~f:uniq_eqn_st ~x:(Env.create()) in
    pb'

  let pipe ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = NunProblem.Print(P)(P) in
        [Format.printf "@[<v2>after uniq equations: %a@]@." PPb.print]
      else []
    and decode _ x = decode x in
    NunTransform.make1
      ~on_encoded
      ~name:"recursion_elim"
      ~encode:(fun p ->
        let p = uniq_eqns_pb p in
        p, ()
      ) ~decode
      ()
end


