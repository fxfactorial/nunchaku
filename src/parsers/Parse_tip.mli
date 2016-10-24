
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Wrapper for TIP} *)

open Nunchaku

type 'a or_error = ('a, string) CCResult.t

val parse_lexbuf : Lexing.lexbuf -> Tip_ast.statement list or_error

val parse_file : string -> Tip_ast.statement list or_error

val parse_stdin : unit -> Tip_ast.statement list or_error

val convert : Tip_ast.statement -> UntypedAST.statement list

val convert_l :
  ?into:UntypedAST.statement CCVector.vector ->
  Tip_ast.statement list ->
  UntypedAST.statement CCVector.vector

(** {2 Parse + convert} *)

val parse :
  ?mode:Parsing_utils.include_mode ->
  ?into:UntypedAST.statement CCVector.vector ->
  [`File of string | `Stdin] ->
  UntypedAST.statement CCVector.vector or_error
