
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lexer} *)

val token : Lexing.lexbuf -> NunParser.token


(** {2 Utils} *)

type 'a or_error = [`Ok of 'a | `Error of string ]

type statement = NunUntypedAST.statement
type term = NunUntypedAST.term
type ty = NunUntypedAST.ty

val parse_file : string -> statement list or_error

val parse_stdin : unit -> statement list or_error

val ty_of_string : string -> ty or_error

val ty_of_string_exn : string -> ty

val term_of_string : string -> term or_error

val term_of_string_exn : string -> term

val statement_of_string : string -> statement or_error

val statement_of_string_exn : string -> statement

module HO : sig
  type inv = NunTerm_ho.OfUntyped.invariant

  module T = NunTerm_ho.Default

  val term_of_str : string -> inv T.t or_error
  val term_of_str_exn : string -> inv T.t
end

