
(** {1 Main program} *)

module E = CCError
module A = UntypedAST
module Utils = Utils
module TI = TermInner

type input =
  | I_nunchaku
  | I_tptp

let list_inputs_ () = "(available choices: nunchaku tptp)"

type output =
  | O_nunchaku
  | O_tptp

let list_outputs_ () = "(available choices: nunchaku tptp)"

(** {2 Options} *)

let input_ = ref I_nunchaku
let output_ = ref O_nunchaku
let print_ = ref false
let print_pipeline_ = ref false
let print_typed_ = ref false
let print_skolem_ = ref false
let print_mono_ = ref false
let print_elim_match_ = ref false
let print_recursion_elim_ = ref false
let print_elim_multi_eqns = ref false
let print_polarize_ = ref false
let print_elim_preds_ = ref false
let print_intro_guards_ = ref false
let print_fo_ = ref false
let print_smt_ = ref false
let timeout_ = ref 30
let version_ = ref false
let file = ref ""
let j = ref 3

let set_file f =
  if !file <> ""
  then raise (Arg.Bad "please provide only one file")
  else file := f

let set_input_ f =
  input_ := match String.lowercase f with
    | "nunchaku" -> I_nunchaku
    | "tptp" -> I_tptp
    | s -> failwith ("unsupported input format: " ^ s)

let set_output_ f =
  output_ := match String.lowercase f with
    | "nunchaku" -> O_nunchaku
    | "tptp" -> O_tptp
    | s -> failwith ("unsupported output format: " ^ s)

(* set debug levels *)
let options_debug_ = Utils.Section.iter
  |> Sequence.map
    (fun (name,sec) ->
      "--debug" ^ (if name="" then "" else "."^name),
      Arg.Int (Utils.Section.set_debug sec),
      " verbosity level for " ^ (if name="" then "all messages" else name))
  |> Sequence.to_rev_list

let options =
  let open CCFun in
  Arg.align ?limit:None @@ List.sort Pervasives.compare @@ (
  options_debug_ @
  [ "--print-input", Arg.Set print_, " print input"
  ; "--print-pipeline", Arg.Set print_pipeline_, " print full pipeline"
  ; "--print-typed", Arg.Set print_typed_, " print input after typing"
  ; "--print-skolem", Arg.Set print_skolem_, " print input after Skolemization"
  ; "--print-mono", Arg.Set print_mono_, " print input after monomorphization"
  ; "--print-elim-match", Arg.Set print_elim_match_,
      " print input after elimination of pattern matching"
  ; "--print-elim-preds", Arg.Set print_elim_preds_,
      " print input after elimination of (co)inductive predicates"
  ; "--print-rec-elim", Arg.Set print_recursion_elim_,
      " print input after elimination of recursive functions"
  ; "--print-elim-multi-eqns", Arg.Set print_elim_multi_eqns,
      " print input after elimination of multiple equations"
  ; "-j", Arg.Set_int j, " set parallelism level"
  ; "--print-polarize", Arg.Set print_polarize_, " print input after polarization"
  ; "--print-intro-guards", Arg.Set print_intro_guards_,
      " print input after introduction of guards"
  ; "--print-fo", Arg.Set print_fo_, " print first-order problem"
  ; "--print-smt", Arg.Set print_smt_, " print SMT problem"
  ; "--print-raw-model", Arg.Set Solver_intf.print_model_, " print raw model"
  ; "--timeout", Arg.Set_int timeout_, " set timeout (in s)"
  ; "--input", Arg.String set_input_, " set input format " ^ list_inputs_ ()
  ; "--output", Arg.String set_output_, " set output format " ^ list_outputs_ ()
  ; "--backtrace", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable stack traces"
  ; "--version", Arg.Set version_, " print version and exit"
  ]
)

let print_version_if_needed () =
  if !version_ then (
    Format.printf "nunchaku %s %s@." Const.version GitVersion.id;
    exit 0
  );
  ()

let parse_file ~input () =
  let open CCError.Infix in
  let src = if !file = "" then `Stdin else `File !file in
  let res =
    try
      match input with
      | I_nunchaku ->
          NunLexer.parse src
      | I_tptp ->
          NunTPTPLexer.parse ~mode:(`Env "TPTP") src
          >|= CCVector.to_seq
          >>= NunTPTPPreprocess.preprocess
    with e -> Utils.err_of_exn e
  in
  E.map_err
    (fun msg -> CCFormat.sprintf "@[<2>could not parse `%s`:@ %s@]" !file msg) res

let print_input_if_needed statements =
  if !print_ then
    Format.printf "@[<v2>input: {@,@[<v>%a@]@]@,}@."
      (CCVector.print ~start:"" ~stop:"" ~sep:"" A.print_statement)
      statements;
  ()

module Pipes = struct
  module HO = TI.Default
  module Typed = TermTyped.Default
  (* typeference *)
  module Step_tyinfer = TypeInference.Make(Typed)(HO)
  (* encodings *)
  module Step_skolem = Skolem.Make(Typed)(HO)
  module Step_mono = Monomorphization.Make(HO)
  module Step_ElimMultipleEqns = ElimMultipleEqns.Make(HO)
  module Step_ElimMatch = ElimPatternMatch.Make(HO)
  module Step_elim_preds = ElimIndPreds.Make(HO)
  module Step_rec_elim = ElimRecursion.Make(HO)
  module Step_polarize = Polarize.Make(HO)
  module Step_intro_guards = IntroGuards.Make(HO)
  (* conversion to FO *)
  module Step_tofo = TermMono.TransFO(HO)(FO.Default)
end

(* build a pipeline, depending on options *)
let make_model_pipeline () =
  let open Transform.Pipe in
  let open Pipes in
  (* setup pipeline *)
  let pipe =
    Step_tyinfer.pipe ~print:!print_typed_  @@@
    Step_skolem.pipe ~print:!print_skolem_ @@@
    Step_mono.pipe ~print:!print_mono_ @@@
    Step_ElimMultipleEqns.pipe
      ~decode:(fun x->x) ~print:!print_elim_multi_eqns @@@
    Step_polarize.pipe ~print:!print_polarize_ @@@
    Step_elim_preds.pipe ~print:!print_elim_preds_ @@@
    Step_rec_elim.pipe ~print:!print_recursion_elim_ @@@
    Step_ElimMatch.pipe ~print:!print_elim_match_ @@@
    Step_intro_guards.pipe ~print:!print_intro_guards_ @@@
    Step_tofo.pipe () @@@
    id
  in
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  CVC4.close_pipe FO.default ~options:CVC4.options_l ~j:!j
    ~pipe ~deadline ~print:!print_fo_ ~print_smt:!print_smt_

(* search for results *)
let rec find_model_ l =
  let module Res = Problem.Res in
  try
  match l() with
    | `Nil -> E.return `Unsat
    | `Cons ((res, conv_back), tail) ->
        match res with
        | Res.Timeout -> E.return `Timeout
        | Res.Unsat -> find_model_ tail
        | Res.Sat m ->
            let m = conv_back m in
            E.return (`Sat m)
  with e -> Utils.err_of_exn e

(* negate the goal *)
let negate_goal stmts =
  let module A = UntypedAST in
  CCVector.map
    (fun st -> match st.A.stmt_value with
      | A.Goal f -> {st with A.stmt_value=A.Goal (A.not_ f); }
      | _ -> st
    ) stmts

(* additional printers *)
let () = Printexc.register_printer
  (function
    | Failure msg -> Some ("failure: " ^ msg)
    | _ -> None
  )

open CCError.Infix

(* model mode *)
let main_model ~output statements =
  (* run pipeline *)
  let cpipe = make_model_pipeline() in
  if !print_pipeline_
    then Format.printf "@[Pipeline: %a@]@." Transform.ClosedPipe.print cpipe;
  Transform.run_closed ~cpipe statements |> find_model_
  >|= fun res ->
  begin match res, output with
  | `Sat m, O_nunchaku ->
      Format.printf "@[<v2>SAT: @,%a@]@."
        (Model.print UntypedAST.print_term) m;
  | `Sat m, O_tptp ->
      Format.printf "@[<v2>%a@]@,@." NunPrintTPTP.print_model m
  | `Unsat, O_nunchaku ->
      (* TODO: check whether we have a "spurious" flag *)
      Format.printf "@[UNSAT@]@."
  | `Unsat, O_tptp ->
      (* TODO: check whether we have a "spurious" flag *)
      Format.printf "@[SZS Status: Unsatisfiable@]@."
  | `Timeout, _ ->
      Format.printf "@[TIMEOUT@]@."
  end;
  ()

(* main *)
let main () =
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  (* parse *)
  parse_file ~input:!input_ ()
  >>= fun statements ->
  print_input_if_needed statements;
  main_model ~output:!output_ statements

let () =
  E.catch (main ())
  ~ok:(fun () -> exit 0)
  ~err:(fun msg ->
    Format.eprintf "%s@." msg;
    exit 1
  )
